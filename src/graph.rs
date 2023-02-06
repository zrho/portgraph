#[cfg(feature = "pyo3")]
use pyo3::prelude::*;
use std::collections::BTreeMap;
use std::fmt::{self, Debug};
use std::iter::FusedIterator;
use thiserror::Error;

use crate::memory::{slab, Slab};
pub use crate::{Direction, EdgeIndex, NodeIndex};

/// The graph's node type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<N> {
    /// Associated node data.
    weight: N,

    /// The first incoming and outgoing edge.
    edges: [Option<EdgeIndex>; 2],
}

impl<N> Node<N> {
    fn relink(&mut self, edge_map: &EdgeMap) {
        for i in 0..=1 {
            self.edges[i] = self.edges[i].and_then(|edge| edge_map.get(&edge)).copied();
        }
    }
}

/// The graph's edge type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge<E> {
    /// Associated edge data.
    weight: E,

    /// The nodes that the edge is connected to.
    ///
    /// The first component is the target and the second component the source of the edge. This
    /// is so that the array can be indexed by `Direction`.
    nodes: [Option<NodeIndex>; 2],

    /// Intrusive linked lists that point to the next edge connected to the edge's endpoints.
    next: [Option<EdgeIndex>; 2],
}

impl<E> Edge<E> {
    fn relink(&mut self, node_map: &NodeMap, edge_map: &EdgeMap) {
        for i in 0..=1 {
            self.next[i] = self.next[i].and_then(|edge| edge_map.get(&edge)).copied();
            self.nodes[i] = self.nodes[i].and_then(|node| node_map.get(&node)).copied();
        }
    }
}

type NodeMap = BTreeMap<NodeIndex, NodeIndex>;
type EdgeMap = BTreeMap<EdgeIndex, EdgeIndex>;

#[derive(Clone, PartialEq, Eq)]
pub struct Graph<N, E> {
    nodes: Slab<NodeIndex, Node<N>>,
    edges: Slab<EdgeIndex, Edge<E>>,
}

impl<N: Debug, E: Debug> Debug for Graph<N, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Graph")
            .field("nodes", &self.nodes)
            .field("edges", &self.edges)
            .finish()
    }
}

impl<N, E> Default for Graph<N, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N, E> Graph<N, E> {
    /// Create a new empty graph.
    pub fn new() -> Self {
        Self::with_capacity(0, 0)
    }

    /// Create a new empty graph with preallocated capacities for nodes and edges.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: Slab::with_capacity(nodes),
            edges: Slab::with_capacity(edges),
        }
    }

    /// Add a node to the graph.
    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.nodes.insert(Node {
            weight,
            edges: [None; 2],
        })
    }

    /// Add a node to the graph with specified incoming and outgoing edges.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let e3 = graph.add_edge(-3);
    /// let n0 = graph.add_node_with_edges(0, [e1, e2], [e3]).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e3]));
    /// ```
    pub fn add_node_with_edges(
        &mut self,
        weight: N,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> Result<NodeIndex, ConnectError> {
        let node = self.add_node(weight);
        self.connect_many(node, incoming, Direction::Incoming, None)?;
        self.connect_many(node, outgoing, Direction::Outgoing, None)?;
        Ok(node)
    }

    /// Add an edge to the graph.
    pub fn add_edge(&mut self, weight: E) -> EdgeIndex {
        self.edges.insert(Edge {
            weight,
            next: [None; 2],
            nodes: [None; 2],
        })
    }

    /// Remove a node from the graph.
    ///
    /// The edges connected to the node will remain in the graph but will become dangling.
    ///
    /// Returns the node's weight if it existed or `None` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let n0 = graph.add_node_with_edges(0, [e1], []).unwrap();
    ///
    /// assert_eq!(graph.remove_node(n0), Some(0));
    /// assert_eq!(graph.remove_node(n0), None);
    /// assert!(graph.has_edge(e1));
    /// assert_eq!(graph.edge_endpoint(e1, Direction::Incoming), None);
    /// ```
    pub fn remove_node(&mut self, node_index: NodeIndex) -> Option<N> {
        let node = self.nodes.remove(node_index)?;

        for direction in Direction::ALL {
            let mut edge_index_next = node.edges[direction.index()];

            while let Some(edge_index) = edge_index_next {
                let edge = &mut self.edges[edge_index];
                edge.nodes[direction.index()] = None;
                edge_index_next = std::mem::take(&mut edge.next[direction.index()]);
            }
        }

        Some(node.weight)
    }

    /// Remove an edge from the graph.
    ///
    /// The nodes that the edge is connected to will remain the graph but will no longer refer to
    /// the deleted edge. This changes the indices of the edges adjacent to a node.
    ///
    /// Returns the edge's weight if it existed or `None` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let e3 = graph.add_edge(-3);
    /// let n0 = graph.add_node_with_edges(0, [e1, e2, e3], []).unwrap();
    ///
    /// assert_eq!(graph.remove_edge(e2), Some(-2));
    /// assert_eq!(graph.remove_edge(e2), None);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e3]));
    /// ```
    pub fn remove_edge(&mut self, e: EdgeIndex) -> Option<E> {
        self.disconnect(e, Direction::Incoming);
        self.disconnect(e, Direction::Outgoing);
        let edge = self.edges.remove(e)?;
        Some(edge.weight)
    }

    /// Check whether the graph has a node with a given index.
    pub fn has_node(&self, n: NodeIndex) -> bool {
        self.nodes.contains(n)
    }

    /// Check whether the graph has an edge with a given index.
    pub fn has_edge(&self, e: EdgeIndex) -> bool {
        self.edges.contains(e)
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected after the edge with index `edge_prev`.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let e3 = graph.add_edge(-3);
    /// let n0 = graph.add_node_with_edges(0, [e1, e3], []).unwrap();
    ///
    /// graph.connect_after(n0, e2, Direction::Incoming, e1).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2, e3]));
    /// ```
    pub fn connect_after(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        edge_prev: EdgeIndex,
    ) -> Result<(), ConnectError> {
        if edge == edge_prev {
            return Err(ConnectError::SameEdge);
        }

        let (edge_data, edge_prev_data) = self
            .edges
            .get_mut_2(edge, edge_prev)
            .ok_or(ConnectError::UnknownEdge)?;

        if edge_prev_data.nodes[direction.index()] != Some(node) {
            return Err(ConnectError::NodeMismatch);
        } else if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        edge_data.nodes[direction.index()] = Some(node);
        edge_data.next[direction.index()] = edge_prev_data.next[direction.index()];
        edge_prev_data.next[direction.index()] = Some(edge);

        Ok(())
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected before all other edges adjacent to the node.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let n0 = graph.add_node(0);
    ///
    /// graph.connect_first(n0, e2, Direction::Incoming).unwrap();
    /// graph.connect_first(n0, e1, Direction::Incoming).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    /// ```
    pub fn connect_first(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let node_data = self.nodes.get_mut(node).ok_or(ConnectError::UnknownNode)?;
        let edge_data = self.edges.get_mut(edge).ok_or(ConnectError::UnknownEdge)?;

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        edge_data.nodes[direction.index()] = Some(node);
        edge_data.next[direction.index()] = node_data.edges[direction.index()];
        node_data.edges[direction.index()] = Some(edge);

        Ok(())
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    pub fn connect(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        edge_prev: Option<EdgeIndex>,
    ) -> Result<(), ConnectError> {
        match edge_prev {
            Some(edge_prev) => self.connect_after(node, edge, direction, edge_prev),
            None => self.connect_first(node, edge, direction),
        }
    }

    /// Connect a collection of edges to incoming or outgoing ports of a node.
    pub fn connect_many(
        &mut self,
        node: NodeIndex,
        edges: impl IntoIterator<Item = EdgeIndex>,
        direction: Direction,
        mut edge_prev: Option<EdgeIndex>,
    ) -> Result<(), ConnectError> {
        for edge in edges {
            self.connect(node, edge, direction, edge_prev)?;
            edge_prev = Some(edge);
        }

        Ok(())
    }

    pub fn connect_last(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let edge_prev = self.node_edges(node, direction).last();
        self.connect(node, edge, direction, edge_prev)
    }

    fn edge_prev(&self, edge_index: EdgeIndex, direction: Direction) -> Option<EdgeIndex> {
        let node_index = self.edge_endpoint(edge_index, direction)?;

        self.node_edges(node_index, direction)
            .skip(1)
            .zip(self.node_edges(node_index, direction))
            .find(|(item, _)| *item == edge_index)
            .map(|(_, prev)| prev)
    }

    /// Disconnect an edge endpoint from a node.
    ///
    /// This operation takes time linear in the number of edges that precede the edge to be
    /// disconnected at the node.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let e3 = graph.add_edge(-3);
    /// let n0 = graph.add_node_with_edges(0, [e1, e2, e3], []).unwrap();
    ///
    /// graph.disconnect(e2, Direction::Incoming);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e3]));
    ///
    /// graph.disconnect(e1, Direction::Incoming);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e3]));
    /// ```
    pub fn disconnect(&mut self, edge_index: EdgeIndex, direction: Direction) {
        if !self.has_edge(edge_index) {
            return;
        }

        let prev = self.edge_prev(edge_index, direction);

        let edge = &mut self.edges[edge_index];
        let node = std::mem::take(&mut edge.nodes[direction.index()]);
        let next = std::mem::take(&mut edge.next[direction.index()]);

        let Some(node) = node else {
            return;
        };

        match prev {
            Some(prev) => self.edges[prev].next[direction.index()] = next,
            None => self.nodes[node].edges[direction.index()] = next,
        }
    }

    pub fn replace_connection(
        &mut self,
        prev: EdgeIndex,
        new: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let n = self
            .edge_endpoint(prev, direction)
            .ok_or(ConnectError::UnknownEdge)?;

        self.connect_after(n, new, direction, prev)?;

        self.disconnect(prev, direction);
        Ok(())
    }

    /// Connect edge to node, inserting to connection list at specified index.
    ///
    /// This operation takes time linear in index.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let n0 = graph.add_node_with_edges(0, [e1], []).unwrap();
    ///
    /// graph.insert_edge(n0, e2, Direction::Incoming, 1);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    ///
    /// ```
    pub fn insert_edge(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        index: usize,
    ) -> Result<(), ConnectError> {
        let edge_prev = if index == 0 {
            None
        } else {
            self.node_edges(node, direction).nth(index - 1)
        };

        self.connect(node, edge, direction, edge_prev)
    }

    /// A reference to the weight of the node with a given index.
    pub fn node_weight(&self, a: NodeIndex) -> Option<&N> {
        Some(&self.nodes.get(a)?.weight)
    }

    /// A mutable reference to the weight of the node with a given index.
    pub fn node_weight_mut(&mut self, a: NodeIndex) -> Option<&mut N> {
        Some(&mut self.nodes.get_mut(a)?.weight)
    }

    /// A reference to the weight of the edge with a given index.
    pub fn edge_weight(&self, e: EdgeIndex) -> Option<&E> {
        Some(&self.edges.get(e)?.weight)
    }

    /// A mutable reference to the weight of the edge with a given index.
    pub fn edge_weight_mut(&mut self, e: EdgeIndex) -> Option<&mut E> {
        Some(&mut self.edges.get_mut(e)?.weight)
    }

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    pub fn edge_endpoint(&self, e: EdgeIndex, direction: Direction) -> Option<NodeIndex> {
        self.edges.get(e)?.nodes[direction.index()]
    }

    /// Iterator over the edges that are connected to a node.
    pub fn node_edges(&self, n: NodeIndex, direction: Direction) -> NodeEdges<'_, N, E> {
        let next = self
            .nodes
            .get(n)
            .and_then(|node| node.edges[direction.index()]);

        NodeEdges {
            graph: self,
            direction,
            next,
        }
    }

    // Iterate over connected nodes.
    pub fn neighbours(
        &self,
        n: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = NodeIndex> + '_ {
        self.node_edges(n, direction)
            .filter_map(move |e| self.edge_endpoint(e, direction.reverse()))
    }

    /// Iterator over the node indices of the graph.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let n0 = graph.add_node(0);
    /// let n1 = graph.add_node(1);
    /// let n2 = graph.add_node(2);
    ///
    /// graph.remove_node(n1);
    ///
    /// assert!(graph.node_indices().eq([n0, n2]));
    /// ```
    pub fn node_indices(&self) -> NodeIndices<N> {
        NodeIndices(self.nodes.iter())
    }

    /// Iterator over the edge indices of the graph.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let e3 = graph.add_edge(-3);
    ///
    /// graph.remove_edge(e2);
    ///
    /// assert!(graph.edge_indices().eq([e1, e3]));
    /// ```
    pub fn edge_indices(&self) -> EdgeIndices<E> {
        EdgeIndices(self.edges.iter())
    }

    /// Iterator over the node weights of the graph.
    pub fn node_weights(&self) -> impl Iterator<Item = &N> + '_ {
        self.nodes.iter().map(|(_, node)| &node.weight)
    }

    /// Iterator over the edge weights of the graph.
    pub fn edge_weights(&self) -> impl Iterator<Item = &E> + '_ {
        self.edges.iter().map(|(_, node)| &node.weight)
    }

    /// Number of nodes in the graph.
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges in the graph.
    #[inline]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Whether the graph has neither nodes nor edges.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.edges.is_empty()
    }

    /// Insert a graph into this graph.
    ///
    /// Returns maps from the node and edge indices in the original graph to the
    /// new indices which were allocated in this graph.
    ///
    /// [Graph::merge_edges] can be used along dangling edges to connect the inserted
    /// subgraph with the rest of the graph
    pub fn insert_graph(&mut self, other: Self) -> (NodeMap, EdgeMap) {
        let node_map: NodeMap = other
            .nodes
            .into_iter()
            .map(|(old_index, node)| {
                let new_index = self.add_node(node.weight);
                self.nodes[new_index].edges = node.edges;
                (old_index, new_index)
            })
            .collect();

        let edge_map: EdgeMap = other
            .edges
            .into_iter()
            .map(|(old_index, edge)| {
                let new_index = self.add_edge(edge.weight);
                self.edges[new_index].nodes = edge.nodes;
                self.edges[new_index].next = edge.next;
                (old_index, new_index)
            })
            .collect();

        for node_index in node_map.values() {
            self.nodes[*node_index].relink(&edge_map);
        }

        for edge_index in edge_map.values() {
            self.edges[*edge_index].relink(&node_map, &edge_map);
        }

        (node_map, edge_map)
    }

    /// Reindex the nodes and edges to be contiguous.
    ///
    /// Returns maps from the previous node and edge indices to their new indices.
    ///
    /// Preserves the order of nodes and edges.
    ///
    /// This method does not release the unused capacity of the graph's storage after
    /// compacting as it might be needed immediately for new insertions. To reduce the
    /// graph's memory allocation call [Graph::shrink_to_fit] after compacting.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// # use std::collections::BTreeMap;
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let n0 = graph.add_node_with_edges(0, [e2], [e1]).unwrap();
    /// let n1 = graph.add_node_with_edges(1, [e1], [e2]).unwrap();
    ///
    /// graph.remove_node(n0);
    /// graph.remove_edge(e1);
    ///
    /// let (node_map, edge_map) = graph.compact();
    ///
    /// assert_eq!(node_map, BTreeMap::from_iter([(n1, n0)]));
    /// assert_eq!(edge_map, BTreeMap::from_iter([(e2, e1)]));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1]));
    /// ```
    pub fn compact(&mut self) -> (NodeMap, EdgeMap) {
        let mut node_map = NodeMap::new();
        let mut edge_map = EdgeMap::new();

        self.nodes.compact(|_, old_index, new_index| {
            node_map.insert(old_index, new_index);
        });

        self.edges.compact(|_, old_index, new_index| {
            edge_map.insert(old_index, new_index);
        });

        for (_, node) in self.nodes.iter_mut() {
            node.relink(&edge_map);
        }

        for (_, edge) in self.edges.iter_mut() {
            edge.relink(&node_map, &edge_map);
        }

        (node_map, edge_map)
    }

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [Graph::compact] before to make indices contiguous.
    pub fn shrink_to_fit(&mut self) {
        self.edges.shrink_to_fit();
        self.nodes.shrink_to_fit();
    }

    /// Merges two edges together:
    /// The edge with index `from` will be removed and its weight returned. The edge with
    /// index `into` will be connected to the node ports that `from` was connected to.
    ///
    /// This method is useful to connect subgraphs inserted via [Graph::insert_graph]
    /// to the rest of the graph.
    ///
    /// # Errors
    ///
    /// Attempting to merge edges which both are already connected to nodes in the same direction
    /// will result in an error.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(-1);
    /// let e2 = graph.add_edge(-2);
    /// let n0 = graph.add_node_with_edges(0, [], [e1]).unwrap();
    /// let n1 = graph.add_node_with_edges(1, [e2], []).unwrap();
    ///
    /// assert_eq!(graph.merge_edges(e2, e1).unwrap(), -2);
    /// assert!(!graph.has_edge(e2));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1]));
    /// assert!(graph.node_edges(n1, Direction::Incoming).eq([e1]));
    /// ```
    pub fn merge_edges(&mut self, from: EdgeIndex, into: EdgeIndex) -> Result<E, MergeEdgesError> {
        if !self.has_edge(from) | !self.has_edge(into) {
            return Err(MergeEdgesError::UnknownEdge);
        }

        for direction in Direction::ALL {
            let from_node = self.edges[from].nodes[direction.index()];
            let into_node = self.edges[into].nodes[direction.index()];

            if from_node.is_some() && into_node.is_some() {
                return Err(MergeEdgesError::AlreadyConnected);
            }
        }

        for direction in Direction::ALL {
            let from_prev = self.edge_prev(from, direction);
            let from_edge = &mut self.edges[from];
            let from_next = std::mem::take(&mut from_edge.next[direction.index()]);
            let from_node = std::mem::take(&mut from_edge.nodes[direction.index()]);

            let Some(from_node) = from_node else {
                continue;
            };

            self.edges[into].nodes[direction.index()] = Some(from_node);
            self.edges[into].next[direction.index()] = from_next;

            match from_prev {
                Some(prev) => self.edges[prev].next[direction.index()] = Some(into),
                None => self.nodes[from_node].edges[direction.index()] = Some(into),
            }
        }

        Ok(self.remove_edge(from).unwrap())
    }
}

/// Error returned by [Graph::connect] and similar methods.
#[derive(Debug, Error)]
pub enum ConnectError {
    #[error("unknown node")]
    UnknownNode,
    #[error("unknown edge")]
    UnknownEdge,
    #[error("node mismatch")]
    NodeMismatch,
    #[error("edge is already connected")]
    AlreadyConnected,
    #[error("can not connect edge relative to itself")]
    SameEdge,
}

/// Error returned by [Graph::merge_edges].
#[derive(Debug, Error)]
pub enum MergeEdgesError {
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
}

/// Iterator created by [Graph::node_edges].
#[derive(Clone)]
pub struct NodeEdges<'a, N, E> {
    graph: &'a Graph<N, E>,
    direction: Direction,
    next: Option<EdgeIndex>,
}

impl<'a, N, E> Iterator for NodeEdges<'a, N, E> {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.graph.edges[self.next?].next[self.direction.index()];
        std::mem::replace(&mut self.next, next)
    }
}

impl<'a, N, E> FusedIterator for NodeEdges<'a, N, E> {}

/// Iterator created by [Graph::node_indices].
pub struct NodeIndices<'a, N: 'a>(slab::Iter<'a, NodeIndex, Node<N>>);

impl<'a, N> Iterator for NodeIndices<'a, N> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for NodeIndices<'a, N> {}
impl<'a, N> FusedIterator for NodeIndices<'a, N> {}

/// Iterator created by [Graph::edge_indices].
pub struct EdgeIndices<'a, E: 'a>(slab::Iter<'a, EdgeIndex, Edge<E>>);

impl<'a, E> Iterator for EdgeIndices<'a, E> {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for EdgeIndices<'a, N> {}
impl<'a, N> FusedIterator for EdgeIndices<'a, N> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    pub fn merge_with_multiple_edges() {
        let mut graph = Graph::<i8, i8>::new();

        let e1 = graph.add_edge(-1);
        let e2 = graph.add_edge(-2);
        let e3 = graph.add_edge(-3);
        let e4 = graph.add_edge(-4);

        let n0 = graph.add_node_with_edges(0, [], [e1, e2, e3]).unwrap();
        let n1 = graph.add_node_with_edges(1, [e1, e4, e3], []).unwrap();

        assert_eq!(graph.merge_edges(e4, e2).unwrap(), -4);
        assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1, e2, e3]));
        assert!(graph.node_edges(n1, Direction::Incoming).eq([e1, e2, e3]));
    }

    #[test]
    pub fn merge_edges_error() {
        let mut graph = Graph::<i8, i8>::new();

        let e1 = graph.add_edge(-1);
        let e2 = graph.add_edge(-2);
        let _ = graph.add_node_with_edges(0, [e1], []).unwrap();
        let _ = graph.add_node_with_edges(1, [e2], []).unwrap();

        assert!(graph.merge_edges(e2, e1).is_err());
    }
}
