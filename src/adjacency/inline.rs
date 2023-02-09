//! Secondary graph data structure with inline arrays for adjacency lists.
use std::mem::take;
use tinyvec::TinyVec;

use super::{Adjacency, AdjacencyMut, AdjacencySlice};
use crate::components::UnmanagedComponent;
use crate::memory::{map::SecondaryMap, EntityIndex};
use crate::{ConnectError, Direction, Insert};

// TODO Implement more of the essential functions, like `merge_edges`

/// Secondary graph data structure with inline arrays for adjacency lists.
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

    pub fn remove_edge(&mut self, index: usize, direction: Direction) -> EI {
        match direction {
            Direction::Incoming => {
                assert!(index < self.ports_incoming as usize);
                self.ports_incoming += 1;
                self.edges.remove(index)
            }
            Direction::Outgoing => {
                let index = index + self.ports_incoming as usize;
                self.edges.remove(index)
            }
        }
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

    pub fn port_count(&self, direction: Direction) -> usize {
        let incoming = self.ports_incoming as usize;
        match direction {
            Direction::Incoming => incoming,
            Direction::Outgoing => self.edges.len() - incoming,
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

    /// Create a new empty graph.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: SecondaryMap::with_capacity(nodes),
            edges: SecondaryMap::with_capacity(edges),
        }
    }

    /// Shrinks the graph's data store as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.edges.shrink_to_fit();
        self.nodes.shrink_to_fit();

        for (_, node_data) in self.nodes.iter_mut() {
            node_data.edges.shrink_to_fit();
        }
    }

    fn connect_last(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        let node_data = &mut self.nodes[node];
        node_data.push_edge(edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = node_data.edge_slice(direction).len() as u16;

        Ok(())
    }

    fn connect_before(
        &mut self,
        node: NI,
        edge: EI,
        before: EI,
        dir: Direction,
    ) -> Result<(), ConnectError> {
        let Some((edge_node, index)) = self.edge_endpoint(before, dir) else {
            return Err(ConnectError::NodeMismatch);
        };

        if edge_node != node {
            return Err(ConnectError::NodeMismatch);
        }

        self.connect_at(node, edge, index, dir)
    }

    fn connect_after(
        &mut self,
        node: NI,
        edge: EI,
        after: EI,
        dir: Direction,
    ) -> Result<(), ConnectError> {
        let Some((edge_node, index)) = self.edge_endpoint(after, dir) else {
            return Err(ConnectError::NodeMismatch);
        };

        if edge_node != node {
            return Err(ConnectError::NodeMismatch);
        }

        self.connect_at(node, edge, index + 1, dir)
    }

    fn connect_at(
        &mut self,
        node: NI,
        edge: EI,
        index: usize,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let node_data = &mut self.nodes[node];
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
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

impl<NI, EI, const NP: usize> Adjacency<NI, EI> for InlineGraph<NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    // TODO: Wrap this up
    type NodeEdges<'a> = std::iter::Copied<std::slice::Iter<'a, EI>> where Self: 'a;
    type Neighbours<'a> = Neighbours<'a, NI, EI, NP> where Self: 'a;

    #[inline]
    fn node_edges(&self, node: NI, dir: Direction) -> Self::NodeEdges<'_> {
        self.node_edges_slice(node, dir).iter().copied()
    }

    #[inline]
    fn edge_endpoint(&self, edge: EI, dir: Direction) -> Option<(NI, usize)> {
        let edge_data = self.edges.get(edge)?;
        let node = edge_data.nodes[dir.index()]?;
        let port = edge_data.ports[dir.index()];
        Some((node, port as usize))
    }

    fn neighbours(&self, n: NI, direction: Direction) -> Self::Neighbours<'_> {
        Neighbours {
            edges: self.node_edges_slice(n, direction).iter(),
            inline_graph: self,
            direction,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Neighbours<'a, NI, EI, const NP: usize>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    EI: Default,
    {
    edges: std::slice::Iter<'a, EI>,
    inline_graph: &'a InlineGraph<NI, EI, NP>,
    direction: Direction,
}

impl<'a, NI, EI, const NP: usize> Iterator for Neighbours<'a, NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    type Item = NI;

    fn next(&mut self) -> Option<Self::Item> {
        self.edges.next().map(move |e| {
            self.inline_graph
                .edge_endpoint(*e, self.direction)
                .unwrap()
                .0
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.edges.size_hint()
    }
}

impl<NI, EI, const NP: usize> AdjacencySlice<NI, EI> for InlineGraph<NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn node_edges_slice(&self, node: NI, dir: Direction) -> &[EI] {
        self.nodes
            .get(node)
            .map(move |node_data| node_data.edge_slice(dir))
            .unwrap_or(&[])
    }
}

impl<NI, EI, const NP: usize> AdjacencyMut<NI, EI> for InlineGraph<NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn connect_many<I>(
        &mut self,
        node: NI,
        edges: I,
        position: Insert<EI>,
        direction: Direction,
    ) -> Result<(), ConnectError>
    where
        I: IntoIterator<Item = EI>,
    {
        let node_data = &mut self.nodes[node];

        if !matches!(position, Insert::Last) {
            todo!()
        }

        let mut completed = true;
        let ports_before = node_data.port_count(direction);

        let edges = edges.into_iter();
        node_data.edges.reserve(edges.size_hint().0);

        let edges = edges.take_while(|edge| {
            completed = self.edges[*edge].nodes[direction.index()].is_none();
            completed
        });

        match direction {
            Direction::Incoming => {
                let index = node_data.ports_incoming as usize;
                node_data.edges.splice(
                    index..index,
                    edges.inspect(|_| node_data.ports_incoming += 1),
                );
            }
            Direction::Outgoing => node_data.edges.extend(edges),
        };

        for (port, edge) in node_data
            .edge_slice(direction)
            .iter()
            .enumerate()
            .skip(ports_before)
        {
            let edge_data = &mut self.edges[*edge];
            edge_data.nodes[direction.index()] = Some(node);
            edge_data.ports[direction.index()] = port as u16;
        }

        if !completed {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        Ok(())
    }

    fn disconnect(&mut self, edge: EI, direction: Direction) -> Option<NI> {
        let Some(edge_data) = self.edges.get_mut(edge) else {
            return None;
        };

        let Some(node) = take(&mut edge_data.nodes[direction.index()]) else {
            return None;
        };

        let port = take(&mut edge_data.ports[direction.index()]) as usize;

        let node_data = &mut self.nodes[node];
        node_data.remove_edge(port, direction);

        for later_edge in &node_data.edge_slice(direction)[port..] {
            self.edges[*later_edge].ports[direction.index()] -= 1;
        }

        Some(node)
    }

    #[inline(always)]
    fn connect(
        &mut self,
        node: NI,
        edge: EI,
        position: Insert<EI>,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        use Insert::*;
        match position {
            First => self.connect_at(node, edge, 0, direction),
            Last => self.connect_last(node, edge, direction),
            Before(before) => self.connect_before(node, edge, before, direction),
            After(after) => self.connect_after(node, edge, after, direction),
            Index(index) => self.connect_at(node, edge, index, direction),
        }
    }

    fn clear_node(&mut self, node: NI) {
        let Some(node_data) = self.nodes.take(node) else {
            return;
        };

        for (_, direction, edge) in node_data.edges_with_ports() {
            let mut edge_data = &mut self.edges[edge];
            edge_data.nodes[direction.index()] = None;
            edge_data.ports[direction.index()] = 0;
        }
    }

    fn clear_edge(&mut self, edge: EI) {
        for direction in Direction::ALL {
            self.disconnect(edge, direction);
        }
    }
}

impl<NI, EI, const NP: usize> UnmanagedComponent<NI, EI> for InlineGraph<NI, EI, NP>
where
    [EI; NP]: tinyvec::Array<Item = EI>,
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn new() -> Self {
        Self::new()
    }

    fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self::with_capacity(nodes, edges)
    }

    fn register_node(&mut self, index: NI) {
        if self.nodes.len() <= index.index() {
            self.nodes.resize(index.index() + 1)
        }
    }

    fn register_edge(&mut self, index: EI) {
        if self.edges.len() <= index.index() {
            self.edges.resize(index.index() + 1)
        }
    }

    fn unregister_node(&mut self, _index: NI) {}

    fn unregister_edge(&mut self, _index: EI) {}

    fn shrink_to(&mut self, nodes: usize, edges: usize) {
        self.nodes.resize(nodes);
        self.edges.resize(edges);
    }

    fn insert_from(
        &mut self,
        other: &Self,
        mut node_map: impl FnMut(NI) -> NI,
        mut edge_map: impl FnMut(EI) -> EI,
    ) {
        for (node, data) in other.nodes.iter() {
            let new_node = node_map(node);
            self.register_node(new_node);
            self.nodes[new_node] = data.clone();
        }
        for (edge, data) in other.edges.iter() {
            let new_edge = edge_map(edge);
            self.register_edge(new_edge);
            self.edges[new_edge] = data.clone();
        }
    }

    fn rekey_node(&mut self, old: NI, new: NI) {
        if let Some(node_data) = self.nodes.rekey(old, new) {
            for (_, direction, edge) in node_data.edges_with_ports() {
                self.edges[edge].nodes[direction.index()] = Some(new);
            }
        }
    }

    fn rekey_edge(&mut self, old: EI, new: EI) {
        if let Some(edge_data) = self.edges.rekey(old, new) {
            for direction in Direction::ALL {
                if let Some(node) = edge_data.nodes[direction.index()] {
                    let port = edge_data.ports[direction.index()] as usize;
                    let node_data = &mut self.nodes[node];
                    node_data.edge_slice_mut(direction)[port] = new;
                }
            }
        }
    }
}