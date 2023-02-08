use std::{iter, ops::Range};
use tinyvec::TinyVec;

use crate::{
    graph::{BasePortGraph, ConnectError, Direction},
    memory::{map::SecondaryMap, EntityIndex},
};

// TODO Implement more of the essential functions, like `disconnect` and `merge_edges`

/// A graph data structure with inline arrays for node ports.
///
/// Every node has a fixed size array it can use to store the edges that are
/// connected to it. When the capacity of this array is exceeded, the edges are
/// instead stored on the heap.
#[derive(Debug, Clone)]
pub struct InlineGraph<NI, EI, const NP: usize = 8>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    EI: Default,
{
    nodes: SecondaryMap<NI, NodeData<EI, NP>>,
    edges: SecondaryMap<EI, EdgeData<NI>>,
}

// TODO: Ideally we would not want to require the edge indices to implement
// `Default`, but this is required for using `tinyvec`. Alternative creates such
// as `smallvec` have `usize` large capacity, which would be a big waste of
// space. Perhaps implement the few aspects of `tinyvec` that we need here ourselves?

#[derive(Debug, Clone, Default)]
struct NodeData<EI: Default, const NP: usize>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
{
    ports_incoming: u16,
    edges: TinyVec<[EI; NP]>,
}

impl<EI, const NP: usize> NodeData<EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    EI: EntityIndex,
{
    pub fn add_incoming_ports(&mut self, ports: impl IntoIterator<Item = EI>) -> Range<usize> {
        let ports = ports.into_iter();
        let range_start = self.ports_incoming as usize;
        let mut range_end = range_start;

        self.edges
            .splice(range_start..range_start, ports.inspect(|_| range_end += 1));

        self.ports_incoming = range_end as u16;

        range_start..range_end
    }

    pub fn add_outgoing_ports(&mut self, ports: impl IntoIterator<Item = EI>) -> Range<usize> {
        let ports = ports.into_iter();
        let range_start = self.edges.len();
        self.edges.extend(ports);
        range_start..self.edges.len()
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

#[derive(Debug, Clone, Default)]
struct EdgeData<NI> {
    ports: [u16; 2],
    nodes: [Option<NI>; 2],
}

impl<NI, EI, const NP: usize> InlineGraph<NI, EI, NP>
where
    NI: EntityIndex,
    EI: EntityIndex,
    [EI; NP]: tinyvec::Array<Item = EI>,
{
    /// Create a new empty graph.
    pub fn new() -> Self {
        Self {
            nodes: SecondaryMap::new(),
            edges: SecondaryMap::new(),
        }
    }

    /// Create a new empty graph with preallocated capacities for nodes and edges.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: SecondaryMap::with_capacity(nodes),
            edges: SecondaryMap::with_capacity(edges),
        }
    }

    /// Adds ports to a node by connecting the given incoming and outgoing edges
    /// at the end of the node's port lists.
    ///
    /// # Errors
    ///
    /// Fails when one of the edges is already connected in the relevant direction.
    /// In the case of an error, the graph will remain unchanged.
    pub fn add_node_ports(
        &mut self,
        node: NI,
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<(), ConnectError> {
        let node_data = &mut self.nodes[node];

        // We collect the iterators so that we can check if the edges are
        // already connected before inserting them into the array. For small
        // numbers of ports this will remain fully on the stack.
        let incoming: TinyVec<[EI; 8]> = incoming.into_iter().collect();
        let outgoing: TinyVec<[EI; 8]> = outgoing.into_iter().collect();

        // Ensure that the edges are not already connected
        for (edges, direction) in [&incoming, &outgoing].into_iter().zip(Direction::ALL) {
            for edge in edges {
                if self.edges[*edge].nodes[direction.index()].is_some() {
                    return Err(ConnectError::AlreadyConnected);
                }
            }
        }

        node_data.edges.reserve(incoming.len() + outgoing.len());
        let incoming_range = node_data.add_incoming_ports(incoming.iter().copied());
        let outgoing_range = node_data.add_outgoing_ports(outgoing.iter().copied());

        for (i, edge) in node_data.edges[incoming_range.clone()].iter().enumerate() {
            let edge_data = &mut self.edges[*edge];
            edge_data.nodes[0] = Some(node);
            edge_data.ports[0] = (i + incoming_range.start) as u16;
        }

        for (i, edge) in node_data.edges[outgoing_range.clone()].iter().enumerate() {
            let edge_data = &mut self.edges[*edge];
            edge_data.nodes[1] = Some(node);
            edge_data.ports[1] = (i + outgoing_range.start) as u16;
        }

        Ok(())
    }

    /// Disconnects all ports of a node.
    pub fn clear_node_ports(&mut self, node: NI) {
        let Some(node_data) = self.nodes.take(node) else {
            return;
        };

        for (_, direction, edge) in node_data.edges_with_ports() {
            let mut edge_data = &mut self.edges[edge];
            edge_data.nodes[direction.index()] = None;
            edge_data.ports[direction.index()] = 0;
        }
    }

    /// Returns the endpoint of an edge in a given direction.
    ///
    /// `None` if the edge does not exist or has no endpoint in that direction.
    #[inline]
    pub fn edge_endpoint(&self, edge: EI, direction: Direction) -> Option<NI> {
        self.edges[edge].nodes[direction.index()]
    }

    /// Returns the index of the port that an edge is connected to.
    ///
    /// `None` if the edge is not connected in the direction.
    #[inline]
    pub fn edge_port(&self, edge: EI, direction: Direction) -> Option<usize> {
        Some(self.edges.get(edge)?.ports[direction.index()] as usize)
    }

    /// Connects an edge to a new node port at the end of the node's port list.
    ///
    /// # Errors
    ///
    /// Fails if the edge is already connected in the direction.
    pub fn connect_last(
        &mut self,
        node: NI,
        direction: Direction,
        edge: EI,
    ) -> Result<(), ConnectError> {
        let node_data = &mut self.nodes[node];
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        node_data.push_edge(edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = node_data.edge_slice(direction).len() as u16;
        Ok(())
    }

    /// Connects an edge to a new node port at an index in the node's port list.
    ///
    /// If the index is out of bounds for the port list, the edge will be connected at the end of the port list instead.
    ///
    /// # Errors
    ///
    /// Fails if the edge is already connected in the direction.
    pub fn connect_at(
        &mut self,
        node: NI,
        direction: Direction,
        index: usize,
        edge: EI,
    ) -> Result<(), ConnectError> {
        let node_data = &mut self.nodes[node];
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        let index = std::cmp::min(index, node_data.edge_slice(direction).len());
        node_data.insert_edge(index, edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = index as u16;

        // Shift the port indices of the edges that come after the newly inserted edge.
        for other_edge in &node_data.edge_slice(direction)[index + 1..] {
            self.edges[*other_edge].ports[direction.index()] += 1;
        }

        Ok(())
    }

    /// Returns a slice containing the indices of the edges connected to a node in a specified direction.
    pub fn node_edges(&self, node: NI, direction: Direction) -> &[EI] {
        self.nodes
            .get(node)
            .map(move |node_data| node_data.edge_slice(direction))
            .unwrap_or(&[])
    }

    /// Changes the key of a node.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    /// Returns whether the node at `old_index` was empty.
    pub fn rekey_node(&mut self, old_index: NI, new_index: NI) -> bool {
        match self.nodes.rekey(old_index, new_index) {
            Some(node_data) => {
                for (_, direction, edge) in node_data.edges_with_ports() {
                    self.edges[edge].nodes[direction.index()] = Some(new_index);
                }

                true
            }
            None => false,
        }
    }

    /// Changes the key of an edge.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    /// Returns whether the edge at `old_index` was empty.
    pub fn rekey_edge(&mut self, old_index: EI, new_index: EI) -> bool {
        match self.edges.rekey(old_index, new_index) {
            Some(edge_data) => {
                for direction in Direction::ALL {
                    if let Some(node) = edge_data.nodes[direction.index()] {
                        let port = edge_data.ports[direction.index()] as usize;
                        let node_data = &mut self.nodes[node];
                        node_data.edge_slice_mut(direction)[port] = new_index;
                    }
                }

                true
            }
            None => false,
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
}

impl<NI, EI, const NP: usize> Default for InlineGraph<NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<NI, EI> BasePortGraph<NI, EI> for InlineGraph<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    type NodeIndicesIterator<'a> = iter::Empty<NI> // TODO: impl
    where
        Self: 'a;

    type NeighboursIterator<'a> = iter::Empty<NI> // TODO: impl
    where
        Self: 'a;

    type NodeEdgesIterator<'a> = iter::Empty<EI> // TODO: impl
    where
        Self: 'a;

    type EdgeIndicesIterator<'a> = iter::Empty<EI> // TODO: impl
    where
        Self: 'a;

    fn new() -> Self {
        Self::new()
    }

    fn with_capacity(nodes: usize, edges: usize, _ports: usize) -> Self {
        Self::with_capacity(nodes, edges)
    }

    fn add_node_unweighted(&mut self) -> NI {
        todo!()
    }

    fn next_node_index(&self) -> NI {
        todo!()
    }

    fn add_node_with_edges_unweighted(
        &mut self,
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<NI, ConnectError> {
        todo!()
    }

    fn add_edge_unweighted(&mut self) -> EI {
        todo!()
    }

    fn remove_node_unweighted(&mut self, node_index: NI) -> bool {
        todo!()
    }

    fn remove_edge_unweighted(&mut self, e: EI) -> bool {
        todo!()
    }

    fn has_node(&self, n: NI) -> bool {
        todo!()
    }

    fn has_edge(&self, e: EI) -> bool {
        todo!()
    }

    fn connect_after(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        edge_prev: EI,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn connect_first(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn connect(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        edge_prev: Option<EI>,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn connect_many(
        &mut self,
        node: NI,
        edges: impl IntoIterator<Item = EI>,
        direction: Direction,
        edge_prev: Option<EI>,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn connect_last(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn disconnect(&mut self, edge_index: EI, direction: Direction) {
        todo!()
    }

    fn replace_connection(
        &mut self,
        prev: EI,
        new: EI,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn insert_edge(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        index: usize,
    ) -> Result<(), ConnectError> {
        todo!()
    }

    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<NI> {
        todo!()
    }

    fn node_edges<'a>(&'a self, n: NI, direction: Direction) -> Self::NodeEdgesIterator<'a> {
        todo!()
    }

    fn neighbours<'a>(&'a self, n: NI, direction: Direction) -> Self::NeighboursIterator<'a> {
        todo!()
    }

    fn node_indices<'a>(&'a self) -> Self::NodeIndicesIterator<'a> {
        todo!()
    }

    fn edge_indices<'a>(&'a self) -> Self::EdgeIndicesIterator<'a> {
        todo!()
    }

    fn node_count(&self) -> usize {
        todo!()
    }

    fn edge_count(&self) -> usize {
        todo!()
    }

    fn port_count(&self) -> usize {
        todo!()
    }

    fn insert_graph(&mut self, other: Self) -> (super::NodeMap, super::EdgeMap) {
        todo!()
    }

    fn compact(&mut self) -> (super::NodeMap, super::EdgeMap) {
        todo!()
    }

    fn shrink_to_fit(&mut self) {
        todo!()
    }

    fn merge_edges_unweighted(&mut self, from: EI, into: EI) -> Result<(), super::MergeEdgesError> {
        todo!()
    }

    fn edge_prev(&self, edge_index: EI, direction: Direction) -> Option<EI> {
        todo!()
    }
}
