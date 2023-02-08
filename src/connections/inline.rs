use std::mem::take;
use tinyvec::TinyVec;

use super::ConnectError;
use crate::{
    memory::{map::SecondaryMap, EntityIndex},
    Direction,
};

// TODO Implement more of the essential functions, like `merge_edges`

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

    /// Extends the ports of `node`.
    ///
    /// Since both incoming and outgoing ports share their storage, this method
    /// needs to shift all outgoing ports of `node` when inserting incoming
    /// ports. To avoid this, prefer to insert incoming before outgoing ports.
    ///
    /// When the number of ports exceeds the number of allowable ports in the
    /// inline storage, the node's ports will be moved to the heap.
    ///
    /// # Errors
    ///
    /// Fails when one of the given edges is already connected. In that case all
    /// the edges preceding the offending one will be connected to the node.
    pub fn connect_many(
        &mut self,
        node: NI,
        edges: impl Iterator<Item = EI>,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let node_data = &mut self.nodes[node];

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

    /// Reserve storage for `n` more incoming or outgoing ports for `node`.
    pub fn reserve_ports(&mut self, node: NI, n: usize) {
        self.nodes[node].edges.reserve(n)
    }

    /// Disconnects all ports of a node.
    pub fn clear_node(&mut self, node: NI) {
        // TODO This could return an owned edge iterator with the old edges in it.
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
    /// Fails when the edge was already connected.
    pub fn connect_last(
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

    /// Connects an edge to a new node port at an index in the node's port list.
    ///
    /// If the index is out of bounds for the port list, the edge will be connected at the end of the port list instead.
    ///
    /// # Errors
    ///
    /// Fails when the edge was already connected.
    pub fn connect_at(&mut self, node: NI, edge: EI, index: usize, direction: Direction) {
        let node_data = &mut self.nodes[node];
        let edge_data = &mut self.edges[edge];

        debug_assert!(edge_data.nodes[direction.index()].is_none());

        let index = std::cmp::min(index, node_data.edge_slice(direction).len());
        node_data.insert_edge(index, edge, direction);
        edge_data.nodes[direction.index()] = Some(node);
        edge_data.ports[direction.index()] = index as u16;

        // Shift the port indices of the edges that come after the newly inserted edge.
        for other_edge in &node_data.edge_slice(direction)[index + 1..] {
            self.edges[*other_edge].ports[direction.index()] += 1;
        }
    }

    /// Disconnects an edge in a given direction, returning the node it was connected to.
    ///
    /// Returns `None` when the edge is not connected.
    ///
    /// This operation is *O(n)* in the number of ports of the node in both directions.
    pub fn disconnect(&mut self, edge: EI, direction: Direction) -> Option<NI> {
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
    pub fn rekey_node(&mut self, old_index: NI, new_index: NI) {
        if let Some(node_data) = self.nodes.rekey(old_index, new_index) {
            for (_, direction, edge) in node_data.edges_with_ports() {
                self.edges[edge].nodes[direction.index()] = Some(new_index);
            }
        }
    }

    /// Changes the key of an edge.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    pub fn rekey_edge(&mut self, old_index: EI, new_index: EI) {
        if let Some(edge_data) = self.edges.rekey(old_index, new_index) {
            for direction in Direction::ALL {
                if let Some(node) = edge_data.nodes[direction.index()] {
                    let port = edge_data.ports[direction.index()] as usize;
                    let node_data = &mut self.nodes[node];
                    node_data.edge_slice_mut(direction)[port] = new_index;
                }
            }
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
