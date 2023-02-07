use std::iter::FusedIterator;

use thiserror::Error;
use tinyvec::TinyVec;

use crate::{
    memory::{slab, EntityIndex, Slab},
    Direction,
};

#[derive(Debug, Clone)]
pub struct Graph<NI, EI: Default> {
    nodes: Slab<NI, NodeData<EI>>,
    edges: Slab<EI, EdgeData<NI>>,
}

const EDGE_LIST_SIZE: usize = 7;

// TODO: Ideally we would not want to require the edge indices to implement
// `Default`, but this is required for using `tinyvec`. Alternative creates such
// as `smallvec` have `usize` large capacity, which would be a big waste of
// space. Perhaps implement the few aspects of `tinyvec` that we need here ourselves?

#[derive(Debug, Clone)]
struct NodeData<EI: Default> {
    ports_incoming: u16,
    edges: TinyVec<[EI; EDGE_LIST_SIZE]>,
}

impl<EI: EntityIndex> NodeData<EI> {
    pub fn new(
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Self {
        let incoming = incoming.into_iter();
        let outgoing = outgoing.into_iter();

        let mut ports_incoming: u16 = 0;

        let edges = incoming
            .inspect(|_| ports_incoming += 1)
            .chain(outgoing)
            .collect();

        Self {
            edges,
            ports_incoming,
        }
    }

    pub fn push_edge(&mut self, edge: EI, direction: Direction) {
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

    pub fn insert_edge(&mut self, index: usize, edge: EI, direction: Direction) {
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
    pub fn edges_with_ports(&self) -> impl Iterator<Item = (u16, Direction, EI)> + '_ {
        (0u16..).zip(&self.edges).map(|(index, edge)| {
            match index.checked_sub(self.ports_incoming) {
                None => (index, Direction::Incoming, *edge),
                Some(port) => (port, Direction::Outgoing, *edge),
            }
        })
    }

    pub fn edge_slice(&self, direction: Direction) -> &[EI] {
        match direction {
            Direction::Incoming => &self.edges[..self.ports_incoming as usize],
            Direction::Outgoing => &self.edges[self.ports_incoming as usize..],
        }
    }

    pub fn edge_slice_mut(&mut self, direction: Direction) -> &mut [EI] {
        match direction {
            Direction::Incoming => &mut self.edges[..self.ports_incoming as usize],
            Direction::Outgoing => &mut self.edges[self.ports_incoming as usize..],
        }
    }
}

#[derive(Debug, Clone)]
struct EdgeData<NI> {
    ports: [u16; 2],
    nodes: [Option<NI>; 2],
}

impl<NI: EntityIndex, EI: EntityIndex> Graph<NI, EI> {
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

    /// Add a node to the graph with specified incoming and outgoing edges.
    ///
    /// ```
    /// # use portgraph::graph_test::Graph;
    /// # use portgraph::Direction;
    /// let mut graph = Graph::new();
    /// let edge0 = graph.add_edge();
    /// let edge1 = graph.add_edge();
    /// let edge2 = graph.add_edge();
    /// let edge3 = graph.add_edge();
    /// let node = graph.add_node([edge0, edge1], [edge2, edge3]).unwrap();
    /// assert_eq!(graph.node_edges(node, Direction::Incoming), [edge0, edge1]);
    /// assert_eq!(graph.node_edges(node, Direction::Outgoing), [edge2, edge3]);
    /// ```
    pub fn add_node(
        &mut self,
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<NI, ConnectError> {
        let node = self.nodes.next_index();
        let node_data = NodeData::new(incoming, outgoing);

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
    pub fn has_node(&self, node: NI) -> bool {
        self.nodes.contains(node)
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
    pub fn node_indices(&self) -> NodeIndices<NI, EI> {
        NodeIndices(self.nodes.iter())
    }

    /// Returns the number of nodes in the graph.
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn add_edge(&mut self) -> EI {
        self.edges.insert(EdgeData {
            ports: [0; 2],
            nodes: [None; 2],
        })
    }

    /// Returns whether the graph has an edge with a given index.
    pub fn has_edge(&self, e: EI) -> bool {
        self.edges.contains(e)
    }

    /// Returns the endpoint of an edge in a given direction.
    ///
    /// `None` if the edge does not exist or has no endpoint in that direction.
    pub fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<NI> {
        self.edges.get(e)?.nodes[direction.index()]
    }

    /// Returns the number of edges in the graph.
    #[inline]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn connect_last(
        &mut self,
        node: NI,
        direction: Direction,
        edge: EI,
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
        node: NI,
        direction: Direction,
        index: usize,
        edge: EI,
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

        // Shift the port indices of the edges that come after the newly inserted edge.
        for other_edge in &node_data.edge_slice(direction)[index + 1..] {
            self.edges[*other_edge].ports[direction.index()] += 1;
        }

        Ok(())
    }

    pub fn node_edges(&self, node: NI, direction: Direction) -> &[EI] {
        self.nodes
            .get(node)
            .map(move |node_data| node_data.edge_slice(direction))
            .unwrap_or(&[])
    }

    #[inline(always)]
    pub fn node_inputs(&self, node: NI) -> &[EI] {
        self.node_edges(node, Direction::Incoming)
    }

    #[inline(always)]
    pub fn node_outputs(&self, node: NI) -> &[EI] {
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
        FN: FnMut(NI, NI),
        FE: FnMut(EI, EI),
    {
        // TODO: Reserve enough space in the slab so we do not need to reallocate

        for (old_index, node) in other.nodes.into_iter() {
            let new_index = self.nodes.next_index();

            rekey_nodes(old_index, new_index);

            for (_, direction, edge) in node.edges_with_ports() {
                other.edges[edge].nodes[direction.index()] = Some(new_index);
            }

            self.nodes.insert(node);
        }

        for (old_index, edge) in other.edges.into_iter() {
            let new_index = self.edges.next_index();

            rekey_edges(old_index, new_index);

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
        FN: FnMut(NI, NI),
        FE: FnMut(EI, EI),
    {
        self.nodes.compact(|node_data, old_index, new_index| {
            rekey_nodes(old_index, new_index);

            for (_, direction, edge) in node_data.edges_with_ports() {
                self.edges[edge].nodes[direction.index()] = Some(new_index);
            }
        });

        self.edges.compact(|edge_data, old_index, new_index| {
            rekey_edges(old_index, new_index);

            for direction in Direction::ALL {
                if let Some(node) = edge_data.nodes[direction.index()] {
                    let port = edge_data.ports[direction.index()] as usize;
                    self.nodes[node].edge_slice_mut(direction)[port] = new_index;
                }
            }
        });
    }
}

impl<NI: EntityIndex, EI: EntityIndex> Default for Graph<NI, EI> {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator created by [Graph::node_indices].
pub struct NodeIndices<'a, NI, EI: Default>(slab::Iter<'a, NI, NodeData<EI>>);

impl<'a, NI: EntityIndex, EI: EntityIndex> Iterator for NodeIndices<'a, NI, EI> {
    type Item = NI;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, NI: EntityIndex, EI: EntityIndex> ExactSizeIterator for NodeIndices<'a, NI, EI> {}
impl<'a, NI: EntityIndex, EI: EntityIndex> FusedIterator for NodeIndices<'a, NI, EI> {}

/// Iterator created by [Graph::edge_indices].
pub struct EdgeIndices<'a, NI, EI>(slab::Iter<'a, EI, EdgeData<NI>>);

impl<'a, NI, EI: EntityIndex> Iterator for EdgeIndices<'a, NI, EI> {
    type Item = EI;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, NI, EI: EntityIndex> ExactSizeIterator for EdgeIndices<'a, NI, EI> {}
impl<'a, NI, EI: EntityIndex> FusedIterator for EdgeIndices<'a, NI, EI> {}

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
