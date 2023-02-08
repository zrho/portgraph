use super::components::{self, Allocator, Connectivity, Weights};
use super::{
    ConnectError, Direction, EdgeIndex, EdgeMap, MergeEdgesError, NodeIndex, NodeMap, PortIndex,
};
use crate::memory::EntityIndex;

/// Trait for graphs that contain an Allocator.
pub trait HasAllocator<'a, NI = NodeIndex, EI = EdgeIndex>
where
    NI: EntityIndex + 'a,
    EI: EntityIndex + 'a,
{
    /// The allocator type.
    type Allocator<'b>: Allocator<NI, EI>
    where
        Self: 'b;
    /// Returns a reference to the allocator.
    fn allocator(&self) -> &Self::Allocator<'_>;
    /// Returns a mutable reference to the allocator.
    fn allocator_mut(&mut self) -> &mut Self::Allocator<'_>;

    /// Returns the number of nodes in the graph.
    ///
    /// See [`Allocator::node_count`].
    #[inline(always)]
    fn node_count(&self) -> usize {
        self.allocator().node_count()
    }

    /// Returns the number of edges in the graph.
    ///
    /// See [`Allocator::edge_count`].
    #[inline(always)]
    fn edge_count(&self) -> usize {
        self.allocator().edge_count()
    }

    /// Check whether the graph has a node with a given index.
    ///
    /// See [`Allocator::has_node`].
    #[inline(always)]
    fn has_node(&self, n: NI) -> bool {
        self.allocator().has_node(n)
    }

    /// Check whether the graph has an edge with a given index.
    ///
    /// See [`Allocator::has_edge`].
    #[inline(always)]
    fn has_edge(&self, e: EI) -> bool {
        self.allocator().has_edge(e)
    }

    /// Whether the graph has neither nodes nor edges.
    ///
    /// See [`Allocator::is_empty`].
    #[inline]
    fn is_empty(&self) -> bool {
        self.allocator().is_empty()
    }

    /// Iterator over the node indices of the graph.
    ///
    /// See [`Allocator::node_indices`].
    #[inline(always)]
    fn node_indices(
        &'a self,
    ) -> <Self::Allocator<'a> as components::Allocator<NI, EI>>::NodeIndicesIterator<'a> {
        self.allocator().node_indices()
    }

    /// Iterator over the edge indices of the graph.
    ///
    /// See [`Allocator::edge_indices`].
    #[inline(always)]
    fn edge_indices(
        &'a self,
    ) -> <Self::Allocator<'a> as components::Allocator<NI, EI>>::EdgeIndicesIterator<'a> {
        self.allocator().edge_indices()
    }
}

/// Trait for graphs that contain a Connectivity component.
pub trait HasConnectivity<'a, NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    NI: EntityIndex + 'a,
    EI: EntityIndex + 'a,
    PI: EntityIndex + 'a,
{
    /// The allocator type.
    type Connectivity<'b>: Connectivity<NI, EI, PI>
    where
        Self: 'b;
    /// Returns a reference to the connectivity component.
    fn connectivity(&self) -> &Self::Connectivity<'_>;
    /// Returns a mutable reference to the connectivity component.
    fn connectivity_mut(&mut self) -> &mut Self::Connectivity<'_>;

    /// Returns the number of edges connected to the given node.
    ///
    /// See [`Connectivity::node_edge_count`].
    fn node_edge_count(&self, node: NI) -> usize {
        self.connectivity().node_edge_count(node)
    }

    /// Returns the number of edges connected to the given node in the given direction.
    ///
    /// See [`Connectivity::node_edge_count_direction`].
    fn node_edge_count_direction(&self, node: NI, direction: Direction) -> usize {
        self.connectivity()
            .node_edge_count_direction(node, direction)
    }

    /// Iterator over the edges that are connected to a node.
    ///
    /// See [`Connectivity::node_edges`].
    fn node_edges(
        &'a self,
        n: NI,
        direction: Direction,
    ) -> <Self::Connectivity<'a> as components::Connectivity<NI, EI, PI>>::NodeEdgesIterator<'a>
    {
        self.connectivity().node_edges(n, direction)
    }

    /// Iterate over connected nodes.
    ///
    /// See [`Connectivity::neighbours`].
    fn neighbours(
        &'a self,
        n: NI,
        direction: Direction,
    ) -> <Self::Connectivity<'a> as components::Connectivity<NI, EI, PI>>::NeighboursIterator<'a>
    {
        self.connectivity().neighbours(n, direction)
    }

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    ///
    /// See [`Connectivity::edge_endpoint`].
    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, PI)> {
        self.connectivity().edge_endpoint(e, direction)
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// Returns the index of the port that was connected.
    ///
    /// See [`Connectivity::connect`].
    fn connect_first(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<PI, ConnectError> {
        self.connectivity_mut().connect_first(node, edge, direction)
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// Returns the index of the port that was connected.
    ///
    /// The edge will be connected after all other edges adjacent to the node.
    ///
    /// See [`Connectivity::connect`].
    fn connect_last(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<PI, ConnectError> {
        self.connectivity_mut().connect_last(node, edge, direction)
    }

    /// Connect edge to node, inserting to connection list at specified index.
    ///
    /// This operation takes time linear in index.
    ///
    /// See [`Connectivity::connect_at`].
    fn connect_at(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        port: PI,
    ) -> Result<(), ConnectError> {
        self.connectivity_mut()
            .connect_at(node, edge, direction, port)
    }

    /// Disconnect an edge endpoint from a node.
    ///
    /// This operation takes time linear in the number of edges that precede the edge to be
    /// disconnected at the node.
    ///
    /// See [`Connectivity::disconnect`].
    fn disconnect(&mut self, edge_index: EI, direction: Direction) {
        self.connectivity_mut().disconnect(edge_index, direction)
    }
}

/// Trait for graphs that contain a Weights component.
pub trait HasWeights<'a, N, E, P, NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    N: 'a,
    E: 'a,
    P: 'a,
    NI: EntityIndex + 'a,
    EI: EntityIndex + 'a,
    PI: EntityIndex + 'a,
{
    /// The weights type.
    type Weights<'b>: Weights<N, E, P, NI, EI, PI>
    where
        Self: 'b, N: 'b, E: 'b, P: 'b, 'a: 'b;
    /// Returns a reference to the weights component.
    fn weights(&self) -> &Self::Weights<'_>;
    /// Returns a mutable reference to the weights component.
    fn weights_mut(&mut self) -> &mut Self::Weights<'_>;

    /// A reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight`].
    fn node_weight(&'a self, a: NI) -> Option<&N> {
        self.weights().node_weight(a)
    }

    /// A mutable reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight_mut`].
    fn node_weight_mut(&'a mut self, a: NI) -> Option<&'a mut N> {
        self.weights_mut().node_weight_mut(a)
    }

    /// Iterator over the node weights of the graph.
    ///
    /// See [`Weights::node_weights`].
    fn node_weights<'b>(
        &'b self,
    ) -> <Self::Weights<'b> as components::Weights<N, E, P, NI, EI, PI>>::NodeWeightsIterator<'b>
    {
        self.weights().node_weights()
    }

    /// A reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight`].
    fn edge_weight(&'a self, e: EI) -> Option<&'a E> {
        self.weights().edge_weight(e)
    }

    /// A mutable reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight_mut`].
    fn edge_weight_mut(&'a mut self, e: EI) -> Option<&'a mut E> {
        self.weights_mut().edge_weight_mut(e)
    }

    /// Iterator over the edge weights of the graph.
    ///
    /// See [`Weights::edge_weights`].
    fn edge_weights<'b>(
        &'b self,
    ) -> <Self::Weights<'b> as components::Weights<N, E, P, NI, EI, PI>>::EdgeWeightsIterator<'b>
    {
        self.weights().edge_weights()
    }

    /// A reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight`].
    fn port_weight(&'a self, e: PI) -> Option<&'a P>  {
        self.weights().port_weight(e.clone())
    }

    /// A mutable reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight_mut`].
    fn port_weight_mut(&'a mut self, e: PI) -> Option<&'a mut P> {
        <Self::Weights<'a>>::port_weight_mut(self.weights_mut(), e)
    }

    /// Iterator over the port weights of the graph.
    ///
    /// See [`Weights::port_weights`].
    fn port_weights(
        &'a self,
    ) -> <Self::Weights<'a> as components::Weights<N, E, P, NI, EI, PI>>::PortWeightsIterator<'a>
    {
        self.weights().port_weights()
    }
}

/// Core trait for directed graphs. Exposes unweighted nodes with edge ports.
///
/// The parameters `NI`, `EI`, and `PI` are respectively the node, edge and port index types.
pub trait WeightedGraph<'a, N: 'a, E: 'a, P: 'a, NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>:
    HasAllocator<'a, NI, EI> + HasConnectivity<'a, NI, EI, PI> + HasWeights<'a, N, E, P, NI, EI, PI>
where
    NI: EntityIndex + 'a,
    EI: EntityIndex + 'a,
    PI: EntityIndex + 'a,
{
    /// Create a new graph with no nodes or edges.
    fn new() -> Self;

    /// Create a new graph pre-allocating space for the given number of nodes and edges.
    fn with_capacity(nodes: usize, edges: usize) -> Self;

    /// Add a new node to the graph and return its index.
    fn add_node(&mut self, weight: N) -> NI {
        let index = self.allocator_mut().new_node();
        self.connectivity_mut().register_node(index);
        self.weights_mut().register_node(index, weight);
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
    fn add_node_with_edges(
        &mut self,
        weight: N,
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<NI, ConnectError> {
        let _index = self.add_node(weight);
        todo!("add edges to the node");
        //self.connectivity().add_edges(index, incoming, outgoing);
        Ok(_index)
    }

    /// Add an edge to the graph.
    fn add_edge(&mut self, weight: E) -> EI {
        let index = self.allocator_mut().new_edge();
        self.connectivity_mut().register_edge(index);
        self.weights_mut().register_edge(index, weight);
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
    fn remove_node(&mut self, index: NI) -> Option<N> {
        self.allocator_mut().remove_node(index);
        self.connectivity_mut().unregister_node(index);
        self.weights_mut().unregister_node(index)
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
    fn remove_edge(&mut self, index: EI) -> Option<E> {
        self.allocator_mut().remove_edge(index);
        self.connectivity_mut().unregister_edge(index);
        self.weights_mut().unregister_edge(index)
    }

    /// Insert a graph into this graph.
    ///
    /// Returns maps from the node and edge indices in the original graph to the
    /// new indices which were allocated in this graph.
    ///
    /// [Graph::merge_edges] can be used along dangling edges to connect the inserted
    /// subgraph with the rest of the graph
    fn insert_graph(&mut self, other: &Self) -> (NodeMap, EdgeMap) {
        let (node_map, edge_map) = self.allocator_mut().insert_graph(other.allocator());
        self.connectivity_mut()
            .insert_graph(other.connectivity(), &node_map, &edge_map);
        self.weights_mut()
            .insert_graph(other.weights(), &node_map, &edge_map);
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
    fn compact(&mut self) -> (NodeMap, EdgeMap) {
        let (node_map, edge_map) = self.allocator_mut().compact();
        self.connectivity_mut().reindex(&node_map, &edge_map);
        self.weights_mut().reindex(&node_map, &edge_map);
        (node_map, edge_map)
    }

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [Graph::compact] before to make indices contiguous.
    fn shrink_to_fit(&mut self) {
        let alloc = self.allocator_mut();
        alloc.shrink_to_fit();
        let nodes = alloc.node_bound();
        let edges = alloc.edge_bound();
        self.connectivity_mut().shrink_to(nodes, edges);
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
    fn merge_edges(&mut self, from: EI, into: EI) -> Result<E, MergeEdgesError> {
        if !self.has_edge(from) | !self.has_edge(into) {
            return Err(MergeEdgesError::UnknownEdge);
        }
        if self.edge_endpoint(from, Direction::Incoming).is_some()
            || self.edge_endpoint(from, Direction::Outgoing).is_some()
        {
            return Err(MergeEdgesError::AlreadyConnected);
        }

        if let Some((from_node, from_port)) = self.edge_endpoint(from, Direction::Outgoing) {
            self.connect_at(from_node, into, Direction::Outgoing, from_port);
        }

        Ok(self.remove_edge(from).unwrap())
    }
}
