use std::iter::FusedIterator;

use thiserror::Error;
use tinyvec::TinyVec;

use crate::{
    memory::{slab, Slab},
    Direction, EdgeIndex, NodeIndex,
};

pub struct Graph<N, E> {
    nodes: Slab<NodeIndex, Node<N>>,
    edges: Slab<EdgeIndex, Edge<E>>,
}

const EDGE_LIST_SIZE: usize = 7;

struct Node<N> {
    weight: N,
    ports_incoming: u16,
    edges: TinyVec<[EdgeIndex; EDGE_LIST_SIZE]>,
}

impl<N> Node<N> {
    pub fn new(weight: N) -> Self {
        Self {
            weight,
            edges: TinyVec::new(),
            ports_incoming: 0,
        }
    }

    pub fn new_with_ports(
        weight: N,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> Self {
        let incoming = incoming.into_iter();
        let outgoing = outgoing.into_iter();

        let mut ports_incoming: u16 = 0;

        let edges = incoming
            .inspect(|_| ports_incoming += 1)
            .chain(outgoing)
            .collect();

        Self {
            weight,
            edges,
            ports_incoming,
        }
    }

    pub fn push_edge(&mut self, edge: EdgeIndex, direction: Direction) {
        match direction {
            Direction::Incoming => {
                self.edges.insert(self.ports_incoming as usize, edge);
                self.ports_incoming += 1;
            }
            Direction::Outgoing => {
                self.edges.push(edge);
            }
        };
    }

    pub fn insert_edge(&mut self, index: usize, edge: EdgeIndex, direction: Direction) {
        match direction {
            Direction::Incoming => {
                assert!(index < self.ports_incoming as usize);
                self.edges.insert(index, edge);
                self.ports_incoming += 1;
            }
            Direction::Outgoing => {
                let index = index + self.ports_incoming as usize;
                self.edges.insert(index, edge);
            }
        };
    }

    #[inline(always)]
    pub fn edges_with_ports(&self) -> impl Iterator<Item = (u16, Direction, EdgeIndex)> + '_ {
        (0u16..).zip(&self.edges).map(|(index, edge)| {
            match index.checked_sub(self.ports_incoming) {
                None => (index, Direction::Incoming, *edge),
                Some(port) => (port, Direction::Outgoing, *edge),
            }
        })
    }

    pub fn edge_slice(&self, direction: Direction) -> &[EdgeIndex] {
        match direction {
            Direction::Incoming => &self.edges[..self.ports_incoming as usize],
            Direction::Outgoing => &self.edges[self.ports_incoming as usize..],
        }
    }

    pub fn edge_slice_mut(&mut self, direction: Direction) -> &mut [EdgeIndex] {
        match direction {
            Direction::Incoming => &mut self.edges[..self.ports_incoming as usize],
            Direction::Outgoing => &mut self.edges[self.ports_incoming as usize..],
        }
    }
}

struct Edge<E> {
    weight: E,
    ports: [u16; 2],
    nodes: [Option<NodeIndex>; 2],
}

impl<N, E> Graph<N, E> {
    /// Create a new empty graph.
    pub fn new() -> Self {
        Self {
            nodes: Slab::new(),
            edges: Slab::new(),
        }
    }

    /// Whether the graph has neither nodes nor edges.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.edges.is_empty()
    }

    /// Add a node to the graph.
    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.nodes.insert(Node::new(weight))
    }

    /// Add a node to the graph with specified incoming and outgoing edges.
    ///
    /// ```
    /// # use portgraph::graph_test::Graph;
    /// # use portgraph::Direction;
    /// let mut graph = Graph::<usize, usize>::new();
    /// let edge0 = graph.add_edge(0);
    /// let edge1 = graph.add_edge(1);
    /// let edge2 = graph.add_edge(2);
    /// let edge3 = graph.add_edge(3);
    /// let node = graph.add_node_with_edges(7, [edge0, edge1], [edge2, edge3]);
    /// assert_eq!(graph.node_edges(node, Direction::Incoming), [edge0, edge1]);
    /// assert_eq!(graph.node_edges(node, Direction::Outgoing), [edge2, edge3]);
    /// ```
    pub fn add_node_with_edges(
        &mut self,
        weight: N,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> NodeIndex {
        self.try_add_node_with_edges(weight, incoming, outgoing)
            .unwrap()
    }

    pub fn try_add_node_with_edges(
        &mut self,
        weight: N,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> Result<NodeIndex, ConnectError> {
        let node = self.nodes.next_index();
        let node_data = Node::new_with_ports(weight, incoming, outgoing);

        let mut rollback = 0;
        let mut error = None;

        for (port, direction, edge) in node_data.edges_with_ports() {
            let Some(edge_data) = self.edges.get_mut(edge) else {
                error = Some(ConnectError::UnknownEdge);
                break;
            };

            if edge_data.nodes[direction.index()].is_some() {
                error = Some(ConnectError::AlreadyConnected);
                break;
            }

            edge_data.nodes[direction.index()] = Some(node);
            edge_data.ports[direction.index()] = port;
            rollback += 1;
        }

        if let Some(error) = error {
            for (_, direction, edge) in node_data.edges_with_ports().take(rollback) {
                let edge_data = &mut self.edges[edge];
                edge_data.nodes[direction.index()] = None;
            }

            return Err(error);
        }

        Ok(self.nodes.insert(node_data))
    }

    /// Returns whether the graph has a node with a given index.
    #[inline]
    pub fn has_node(&self, node: NodeIndex) -> bool {
        self.nodes.contains(node)
    }

    /// Returns a reference to the weight of the node with a given index.
    #[inline]
    pub fn node_weight(&self, a: NodeIndex) -> Option<&N> {
        Some(&self.nodes.get(a)?.weight)
    }

    /// Returns a mutable reference to the weight of the node with a given index.
    #[inline]
    pub fn node_weight_mut(&mut self, a: NodeIndex) -> Option<&mut N> {
        Some(&mut self.nodes.get_mut(a)?.weight)
    }

    /// Iterates over the node indices of the graph.
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
    #[inline]
    pub fn node_indices(&self) -> NodeIndices<N> {
        NodeIndices(self.nodes.iter())
    }

    /// Returns the number of nodes in the graph.
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn add_edge(&mut self, weight: E) -> EdgeIndex {
        self.edges.insert(Edge {
            weight,
            ports: [0; 2],
            nodes: [None; 2],
        })
    }

    /// Returns whether the graph has an edge with a given index.
    pub fn has_edge(&self, e: EdgeIndex) -> bool {
        self.edges.contains(e)
    }

    /// Returns a reference to the weight of the edge with a given index.
    pub fn edge_weight(&self, e: EdgeIndex) -> Option<&E> {
        Some(&self.edges.get(e)?.weight)
    }

    /// Returns a mutable reference to the weight of the edge with a given index.
    pub fn edge_weight_mut(&mut self, e: EdgeIndex) -> Option<&mut E> {
        Some(&mut self.edges.get_mut(e)?.weight)
    }

    /// Returns the endpoint of an edge in a given direction.
    ///
    /// `None` if the edge does not exist or has no endpoint in that direction.
    pub fn edge_endpoint(&self, e: EdgeIndex, direction: Direction) -> Option<NodeIndex> {
        self.edges.get(e)?.nodes[direction.index()]
    }

    /// Returns the number of edges in the graph.
    #[inline]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn connect_last(&mut self, node: NodeIndex, direction: Direction, edge: EdgeIndex) {
        self.try_connect_last(node, direction, edge).unwrap();
    }

    pub fn try_connect_last(
        &mut self,
        node: NodeIndex,
        direction: Direction,
        edge: EdgeIndex,
    ) -> Result<(), ConnectError> {
        let node_data = self.nodes.get_mut(node).ok_or(ConnectError::UnknownNode)?;
        let edge_data = self.edges.get_mut(edge).ok_or(ConnectError::UnknownEdge)?;

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        node_data.push_edge(edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = node_data.edge_slice(direction).len() as u16;
        Ok(())
    }

    pub fn connect_at(
        &mut self,
        node: NodeIndex,
        direction: Direction,
        index: usize,
        edge: EdgeIndex,
    ) {
        self.try_connect_at(node, direction, index, edge).unwrap()
    }

    pub fn try_connect_at(
        &mut self,
        node: NodeIndex,
        direction: Direction,
        index: usize,
        edge: EdgeIndex,
    ) -> Result<(), ConnectError> {
        let node_data = self.nodes.get_mut(node).ok_or(ConnectError::UnknownNode)?;
        let edge_data = self.edges.get_mut(edge).ok_or(ConnectError::UnknownEdge)?;

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        } else if index >= node_data.edge_slice(direction).len() {
            return Err(ConnectError::OutOfBounds);
        }

        node_data.insert_edge(index, edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = index as u16;
        Ok(())
    }

    pub fn node_edges(&self, node: NodeIndex, direction: Direction) -> &[EdgeIndex] {
        self.nodes
            .get(node)
            .map(move |node_data| node_data.edge_slice(direction))
            .unwrap_or(&[])
    }

    #[inline(always)]
    pub fn node_inputs(&self, node: NodeIndex) -> &[EdgeIndex] {
        self.node_edges(node, Direction::Incoming)
    }

    #[inline(always)]
    pub fn node_outputs(&self, node: NodeIndex) -> &[EdgeIndex] {
        self.node_edges(node, Direction::Outgoing)
    }

    /// Insert a graph into this graph.
    ///
    /// Calls rekey functions for the nodes and then for the edges in the inserted graph.
    ///
    /// [Graph::merge_edges] can be used along dangling edges to connect the inserted
    /// subgraph with the rest of the graph
    pub fn insert_graph<FN, FE>(
        &mut self,
        mut other: Self,
        mut rekey_nodes: FN,
        mut rekey_edges: FE,
    ) where
        FN: FnMut(&mut N, NodeIndex, NodeIndex),
        FE: FnMut(&mut E, EdgeIndex, EdgeIndex),
    {
        // TODO: Reserve enough space in the slab so we do not need to reallocate

        for (old_index, mut node) in other.nodes.into_iter() {
            let new_index = self.nodes.next_index();

            rekey_nodes(&mut node.weight, old_index, new_index);

            for (_, direction, edge) in node.edges_with_ports() {
                other.edges[edge].nodes[direction.index()] = Some(new_index);
            }

            self.nodes.insert(node);
        }

        for (old_index, mut edge) in other.edges.into_iter() {
            let new_index = self.edges.next_index();

            rekey_edges(&mut edge.weight, old_index, new_index);

            for direction in Direction::ALL {
                if let Some(node) = edge.nodes[direction.index()] {
                    let port = edge.ports[direction.index()] as usize;
                    self.nodes[node].edge_slice_mut(direction)[port] = new_index;
                }
            }

            self.edges.insert(edge);
        }
    }

    /// Create a new empty graph with preallocated capacities for nodes and edges.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: Slab::with_capacity(nodes),
            edges: Slab::with_capacity(edges),
        }
    }

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [Graph::compact] before to make indices contiguous.
    pub fn shrink_to_fit(&mut self) {
        self.edges.shrink_to_fit();
        self.nodes.shrink_to_fit();

        for (_, node_data) in self.nodes.iter_mut() {
            node_data.edges.shrink_to_fit();
        }
    }

    pub fn compact<FN, FE>(&mut self, mut rekey_nodes: FN, mut rekey_edges: FE)
    where
        FN: FnMut(&mut N, NodeIndex, NodeIndex),
        FE: FnMut(&mut E, EdgeIndex, EdgeIndex),
    {
        self.nodes.compact(|node_data, old_index, new_index| {
            rekey_nodes(&mut node_data.weight, old_index, new_index);

            for (_, direction, edge) in node_data.edges_with_ports() {
                self.edges[edge].nodes[direction.index()] = Some(new_index);
            }
        });

        self.edges.compact(|edge_data, old_index, new_index| {
            rekey_edges(&mut edge_data.weight, old_index, new_index);

            for direction in Direction::ALL {
                if let Some(node) = edge_data.nodes[direction.index()] {
                    let port = edge_data.ports[direction.index()] as usize;
                    self.nodes[node].edge_slice_mut(direction)[port] = new_index;
                }
            }
        });
    }
}

impl<N, E> Default for Graph<N, E> {
    fn default() -> Self {
        Self::new()
    }
}

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

/// Error returned by [Graph::connect_last] and similar methods.
#[derive(Debug, Error)]
pub enum ConnectError {
    #[error("unknown node")]
    UnknownNode,
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
    #[error("port index is out of bounds")]
    OutOfBounds,
}

impl<N, E> std::ops::Index<NodeIndex> for Graph<N, E> {
    type Output = N;

    #[inline(always)]
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.nodes.get(index).unwrap().weight
    }
}

impl<N, E> std::ops::IndexMut<NodeIndex> for Graph<N, E> {
    #[inline(always)]
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.nodes.get_mut(index).unwrap().weight
    }
}

impl<N, E> std::ops::Index<EdgeIndex> for Graph<N, E> {
    type Output = E;

    #[inline(always)]
    fn index(&self, index: EdgeIndex) -> &Self::Output {
        &self.edges.get(index).unwrap().weight
    }
}

impl<N, E> std::ops::IndexMut<EdgeIndex> for Graph<N, E> {
    #[inline(always)]
    fn index_mut(&mut self, index: EdgeIndex) -> &mut Self::Output {
        &mut self.edges.get_mut(index).unwrap().weight
    }
}
