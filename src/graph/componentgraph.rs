use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use thiserror::Error;

use crate::adjacency::AdjacencyMut;
use crate::components::{Allocator, UnmanagedComponent, Weights};
use crate::memory::EntityIndex;
use crate::Insert;
use crate::{ConnectError, Direction};
use crate::{EdgeIndex, NodeIndex};

type DefaultAllocator<NI, EI> = PhantomData<(NI, EI)>; // TODO: define a good default
type DefaultAdjacency<NI, EI> = PhantomData<(NI, EI)>; // TODO: define a good default
type DefaultWeights<N, E, P, NI, EI> = PhantomData<(N, E, P, NI, EI)>; // TODO: define a good default

pub struct PortGraph<
    N,
    E = (),
    P = (),
    NI = NodeIndex,
    EI = EdgeIndex,
    Ac = DefaultAllocator<NI, EI>,
    Adj = DefaultAdjacency<NI, EI>,
    Ws = DefaultWeights<N, E, P, NI, EI>,
> {
    allocator: Ac,
    adjacency: Adj,
    weights: Ws,
    phantom_data: PhantomData<(N, E, P, NI, EI)>,
}

impl<N, E, P, NI, EI, Ac, Adj, Ws> PortGraph<N, E, P, NI, EI, Ac, Adj, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    Ac: Allocator<NI, EI>,
{
    /// Returns a reference to the allocator.
    #[inline(always)]
    pub fn allocator(&self) -> &Ac {
        &self.allocator
    }
    /// Returns a mutable reference to the allocator.
    #[inline(always)]
    pub fn allocator_mut(&mut self) -> &mut Ac {
        &mut self.allocator
    }

    /// Returns the number of nodes in the graph.
    ///
    /// See [`Allocator::node_count`].
    #[inline(always)]
    pub fn node_count(&self) -> usize {
        self.allocator().node_count()
    }

    /// Returns the number of edges in the graph.
    ///
    /// See [`Allocator::edge_count`].
    #[inline(always)]
    pub fn edge_count(&self) -> usize {
        self.allocator().edge_count()
    }

    /// Check whether the graph has a node with a given index.
    ///
    /// See [`Allocator::has_node`].
    #[inline(always)]
    pub fn has_node(&self, n: NI) -> bool {
        self.allocator().has_node(n)
    }

    /// Check whether the graph has an edge with a given index.
    ///
    /// See [`Allocator::has_edge`].
    #[inline(always)]
    pub fn has_edge(&self, e: EI) -> bool {
        self.allocator().has_edge(e)
    }

    /// Whether the graph has neither nodes nor edges.
    ///
    /// See [`Allocator::is_empty`].
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.allocator().is_empty()
    }

    /// Iterator over the node indices of the graph.
    ///
    /// See [`Allocator::node_indices`].
    #[inline(always)]
    pub fn node_indices(&self) -> Ac::NodeIndices<'_> {
        self.allocator().node_indices()
    }

    /// Iterator over the edge indices of the graph.
    ///
    /// See [`Allocator::edge_indices`].
    #[inline(always)]
    pub fn edge_indices(&self) -> Ac::EdgeIndices<'_> {
        self.allocator().edge_indices()
    }
}

impl<N, E, P, NI, EI, Ac, Adj, Ws> PortGraph<N, E, P, NI, EI, Ac, Adj, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    Adj: AdjacencyMut<NI, EI>,
{
    /// Returns a reference to the adjacency component.
    #[inline(always)]
    pub fn adjacency(&self) -> &Adj {
        &self.adjacency
    }
    /// Returns a mutable reference to the adjacency component.
    #[inline(always)]
    pub fn adjacency_mut(&mut self) -> &mut Adj {
        &mut self.adjacency
    }

    /// Returns the number of edges connected to the given node.
    ///
    /// See [`Adjacency::node_edge_count`].
    #[inline(always)]
    pub fn node_edge_count(&self, node: NI) -> usize {
        self.adjacency().node_edge_count(node)
    }

    /// Iterator over the edges that are connected to a node.
    ///
    /// See [`Adjacency::node_edges`].
    #[inline(always)]
    pub fn node_edges(&self, n: NI, direction: Direction) -> Adj::NodeEdges<'_> {
        self.adjacency().node_edges(n, direction)
    }

    /// Iterate over connected nodes.
    ///
    /// See [`Adjacency::neighbours`].
    #[inline(always)]
    pub fn neighbours(&self, n: NI, direction: Direction) -> Adj::Neighbours<'_> {
        self.adjacency().neighbours(n, direction)
    }

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    ///
    /// See [`Adjacency::edge_endpoint`].
    #[inline(always)]
    pub fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, usize)> {
        self.adjacency().edge_endpoint(e, direction)
    }

    /// Connect edge to node, inserting to connection list at specified index.
    ///
    /// This operation takes time linear in index.
    ///
    /// See [`Adjacency::connect_at`].
    #[inline(always)]
    fn connect(
        &mut self,
        node: NI,
        edge: EI,
        position: Insert<EI>,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        self.adjacency_mut()
            .connect(node, edge, position, direction)
    }

    /// Disconnect an edge endpoint from a node.
    ///
    /// This operation takes time linear in the number of edges that precede the edge to be
    /// disconnected at the node.
    ///
    /// See [`Adjacency::disconnect`].
    #[inline(always)]
    pub fn disconnect(&mut self, edge_index: EI, direction: Direction) -> Option<NI> {
        self.adjacency_mut().disconnect(edge_index, direction)
    }
}

impl<N, E, P, NI, EI, Ac, Adj, Ws> PortGraph<N, E, P, NI, EI, Ac, Adj, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    Ws: Weights<N, E, P, NI, EI>,
{
    /// Returns a reference to the weights component.
    #[inline(always)]
    pub fn weights(&self) -> &Ws {
        &self.weights
    }
    /// Returns a mutable reference to the weights component.
    #[inline(always)]
    pub fn weights_mut(&mut self) -> &mut Ws {
        &mut self.weights
    }

    /// A reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight`].
    #[inline(always)]
    pub fn node_weight(&self, a: NI) -> Option<&N> {
        self.weights().node_weight(a)
    }

    /// A mutable reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight_mut`].
    #[inline(always)]
    pub fn node_weight_mut(&mut self, a: NI) -> Option<&mut N> {
        self.weights_mut().node_weight_mut(a)
    }

    /// Iterator over the node weights of the graph.
    ///
    /// See [`Weights::node_weights`].
    #[inline(always)]
    pub fn node_weights(&self) -> Ws::NodeWeights<'_> {
        self.weights().node_weights()
    }

    /// A reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight`].
    #[inline(always)]
    pub fn edge_weight(&self, e: EI) -> Option<&E> {
        self.weights().edge_weight(e)
    }

    /// A mutable reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight_mut`].
    #[inline(always)]
    pub fn edge_weight_mut(&mut self, e: EI) -> Option<&mut E> {
        self.weights_mut().edge_weight_mut(e)
    }

    /// Iterator over the edge weights of the graph.
    ///
    /// See [`Weights::edge_weights`].
    #[inline(always)]
    pub fn edge_weights(&self) -> Ws::EdgeWeights<'_> {
        self.weights().edge_weights()
    }

    /// A reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight`].
    #[inline(always)]
    pub fn port_weight(&self, e: usize, dir: Direction) -> Option<&P> {
        self.weights().port_weight(e, dir)
    }

    /// A mutable reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight_mut`].
    #[inline(always)]
    pub fn port_weight_mut(&mut self, e: usize, dir: Direction) -> Option<&mut P> {
        self.weights_mut().port_weight_mut(e, dir)
    }

    /// Iterator over the port weights of the graph.
    ///
    /// See [`Weights::port_weights`].
    #[inline(always)]
    pub fn port_weights(&self, dir: Direction) -> Ws::PortWeights<'_> {
        self.weights().port_weights(dir)
    }
}

impl<N, E, P, NI, EI, Ac, Adj, Ws> PortGraph<N, E, P, NI, EI, Ac, Adj, Ws>
where
    NI: EntityIndex + Hash, // TODO: Remove the NodeMaps and drop the Hash requirement.
    EI: EntityIndex + Hash, // TODO: Remove the EdgeMaps and drop the Hash requirement.
    Ac: Allocator<NI, EI>,
    Adj: AdjacencyMut<NI, EI> + UnmanagedComponent<NI, EI>,
    Ws: Weights<N, E, P, NI, EI> + UnmanagedComponent<NI, EI>,
    N: Default, // TODO: Not ideal, but needed while removing the weights.
    E: Default,
    P: Default,
{
    /// Create a new graph with no nodes or edges.
    pub fn new() -> Self {
        Self {
            allocator: Ac::new(),
            adjacency: Adj::new(),
            weights: Ws::new(),
            phantom_data: PhantomData,
        }
    }

    /// Create a new graph pre-allocating space for the given number of nodes and edges.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            allocator: Ac::with_capacity(nodes, edges),
            adjacency: Adj::with_capacity(nodes, edges),
            weights: Ws::with_capacity(nodes, edges),
            phantom_data: PhantomData,
        }
    }

    /// Add a new node to the graph and return its index.
    pub fn add_node(&mut self, weight: N) -> NI {
        let index = self.allocator_mut().new_node();
        self.adjacency_mut().register_node(index);
        self.weights_mut().register_node(index);
        *self.weights_mut().node_weight_mut(index).unwrap() = weight;
        index
    }

    /// Add a node to the graph with specified incoming and outgoing edges.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph, WeightedPortGraph};
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
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<NI, ConnectError> {
        let node = self.add_node(weight);
        for edge in incoming {
            self.connect(node, edge, Insert::Last, Direction::Incoming);
        }
        for edge in outgoing {
            self.connect(node, edge, Insert::Last, Direction::Outgoing);
        }
        Ok(node)
    }

    /// Add an edge to the graph.
    pub fn add_edge(&mut self, weight: E) -> EI {
        let index = self.allocator_mut().new_edge();
        self.adjacency_mut().register_edge(index);
        self.weights_mut().register_edge(index);
        *self.weights_mut().edge_weight_mut(index).unwrap() = weight;
        index
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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph, WeightedPortGraph};
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
    pub fn remove_node(&mut self, index: NI) -> Option<N> {
        self.allocator_mut().remove_node(index);
        self.adjacency_mut().unregister_node(index);
        let weight = self.weights_mut().node_weight_mut(index);
        if let Some(weight) = weight {
            let weight = std::mem::replace(weight, N::default());
            self.weights_mut().unregister_node(index);
            Some(weight)
        } else {
            None
        }
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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph, WeightedPortGraph};
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
    pub fn remove_edge(&mut self, index: EI) -> Option<E> {
        self.allocator_mut().remove_edge(index);
        self.adjacency_mut().unregister_edge(index);
        let weight = self.weights_mut().edge_weight_mut(index);
        if let Some(weight) = weight {
            let weight = std::mem::replace(weight, E::default());
            self.weights_mut().unregister_edge(index);
            Some(weight)
        } else {
            None
        }
    }

    /// Insert a graph into this graph.
    ///
    /// Returns maps from the node and edge indices in the original graph to the
    /// new indices which were allocated in this graph.
    ///
    /// [Graph::merge_edges] can be used along dangling edges to connect the inserted
    /// subgraph with the rest of the graph
    pub fn insert_graph(&mut self, other: &Self) -> (HashMap<NI, NI>, HashMap<EI, EI>) {
        let mut node_map = HashMap::with_capacity(other.node_count());
        let mut edge_map = HashMap::with_capacity(other.edge_count());
        self.allocator_mut().insert_from(
            other.allocator(),
            |old, new| {node_map.insert(old, new);},
            |old, new| {edge_map.insert(old, new);},
        );
        self.adjacency_mut().insert_from(
            other.adjacency(),
            |i| *node_map.get(&i).unwrap(),
            |i| *edge_map.get(&i).unwrap(),
        );
        self.weights_mut().insert_from(
            other.weights(),
            |i| *node_map.get(&i).unwrap(),
            |i| *edge_map.get(&i).unwrap(),
        );
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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// # use std::collections::BTreeMap;
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([e2], [e1]).unwrap();
    /// let n1 = graph.add_node_with_edges_unweighted([e1], [e2]).unwrap();
    ///
    /// graph.remove_node_unweighted(n0);
    /// graph.remove_edge_unweighted(e1);
    ///
    /// let (node_map, edge_map) = graph.compact();
    ///
    /// assert_eq!(node_map, BTreeMap::from_iter([(n1, n0)]));
    /// assert_eq!(edge_map, BTreeMap::from_iter([(e2, e1)]));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1]));
    /// ```
    pub fn compact(&mut self) -> (HashMap<NI, NI>, HashMap<EI, EI>) {
        let mut node_map = HashMap::with_capacity(self.node_count());
        let mut edge_map = HashMap::with_capacity(self.edge_count());
        self.allocator_mut().compact(
            |old, new| {node_map.insert(old, new);},
            |old, new| {edge_map.insert(old, new);},
        );
        self.adjacency_mut().reindex(
            |i| *node_map.get(&i).unwrap(),
            |i| *edge_map.get(&i).unwrap(),
        );
        self.weights_mut().reindex(
            |i| *node_map.get(&i).unwrap(),
            |i| *edge_map.get(&i).unwrap(),
        );
        (node_map, edge_map)
    }

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [Graph::compact] before to make indices contiguous.
    pub fn shrink_to_fit(&mut self) {
        let alloc = self.allocator_mut();
        alloc.shrink_to_fit();
        let nodes = alloc.node_bound();
        let edges = alloc.edge_bound();
        self.adjacency_mut().shrink_to(nodes, edges);
        self.weights_mut().shrink_to(nodes, edges);
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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph, WeightedPortGraph};
    /// let mut graph = Graph::<i8, i8>::new();
    ///
    /// let e1 = graph.add_edge(1);
    /// let e2 = graph.add_edge(2);
    /// let n0 = graph.add_node_with_edges(-1, [], [e1]).unwrap();
    /// let n1 = graph.add_node_with_edges(-2, [e2], []).unwrap();
    ///
    /// assert_eq!(graph.merge_edges(e2, e1).unwrap(), 2);
    /// assert!(!graph.has_edge(e2));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1]));
    /// assert!(graph.node_edges(n1, Direction::Incoming).eq([e1]));
    /// ```
    pub fn merge_edges(&mut self, from: EI, into: EI) -> Result<E, MergeEdgesError> {
        if !self.has_edge(from) | !self.has_edge(into) {
            return Err(MergeEdgesError::UnknownEdge);
        }
        if self.edge_endpoint(from, Direction::Incoming).is_some()
            || self.edge_endpoint(from, Direction::Outgoing).is_some()
        {
            return Err(MergeEdgesError::AlreadyConnected);
        }

        if let Some((from_node, from_port)) = self.edge_endpoint(from, Direction::Outgoing) {
            self.connect(
                from_node,
                into,
                Insert::Index(from_port),
                Direction::Outgoing,
            ).map_err(|_| MergeEdgesError::AlreadyConnected)?;
        }

        Ok(self.remove_edge(from).unwrap())
    }
}

/// Error returned by [Graph::merge_edges].
#[derive(Debug, Error)]
pub enum MergeEdgesError {
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        //let mut graph: PortGraph<usize, usize, usize> = PortGraph::new();
        //assert_eq!(graph.node_count(), 0);
        //assert_eq!(graph.edge_count(), 0);
    }
}
