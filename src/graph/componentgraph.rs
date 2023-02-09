use std::marker::PhantomData;

use super::components::{Allocator, Connectivity, Weights, MergeEdgesError, NodeMap, EdgeMap, NodeIndex, EdgeIndex, PortIndex};
use super::{ConnectError, Direction};
use crate::memory::EntityIndex;

pub struct DefaultAllocator<NI, EI> {
    nodes: Vec<NI>,
    edges: Vec<EI>,
}

pub struct DefaultConnectivity<NI, EI, PI> {
    nodes: Vec<Vec<(EI, Direction, PI)>>,
    edges: Vec<(NI, NI)>,
}

pub struct DefaultWeights<N, E, P, NI, EI, PI>(PhantomData<(N, E, P, NI, EI, PI)>);

pub struct Graph<
    N,
    E,
    P,
    NI = NodeIndex,
    EI = EdgeIndex,
    PI = PortIndex,
    Ac = DefaultAllocator<NI, EI>,
    Ct = DefaultConnectivity<NI, EI, PI>,
    Ws = DefaultWeights<N, E, P, NI, EI, PI>,
> {
    allocator: Ac,
    connectivity: Ct,
    weights: Ws,
    PhantomData: PhantomData<(N, E, P, NI, EI, PI)>,
}

impl<N, E, P, NI, EI, PI, Ac, Ct, Ws> Graph<N, E, P, NI, EI, PI, Ac, Ct, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
    Ac: Allocator<NI, EI>,
{
    /// Returns a reference to the allocator.
    pub fn allocator(&self) -> &Ac {
        &self.allocator
    }
    /// Returns a mutable reference to the allocator.
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
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.allocator().is_empty()
    }

    /// Iterator over the node indices of the graph.
    ///
    /// See [`Allocator::node_indices`].
    #[inline(always)]
    pub fn node_indices(&self) -> Ac::NodeIndicesIterator<'_> {
        self.allocator().node_indices()
    }

    /// Iterator over the edge indices of the graph.
    ///
    /// See [`Allocator::edge_indices`].
    #[inline(always)]
    pub fn edge_indices(&self) -> Ac::EdgeIndicesIterator<'_> {
        self.allocator().edge_indices()
    }
}

impl<N, E, P, NI, EI, PI, Ac, Ct, Ws> Graph<N, E, P, NI, EI, PI, Ac, Ct, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
    Ct: Connectivity<NI, EI, PI>,
{
    /// Returns a reference to the connectivity component.
    pub fn connectivity(&self) -> &Ct {
        &self.connectivity
    }
    /// Returns a mutable reference to the connectivity component.
    pub fn connectivity_mut(&mut self) -> &mut Ct {
        &mut self.connectivity
    }

    /// Returns the number of edges connected to the given node.
    ///
    /// See [`Connectivity::node_edge_count`].
    pub fn node_edge_count(&self, node: NI) -> usize {
        self.connectivity().node_edge_count(node)
    }

    /// Returns the number of edges connected to the given node in the given direction.
    ///
    /// See [`Connectivity::node_edge_count_direction`].
    pub fn node_edge_count_direction(&self, node: NI, direction: Direction) -> usize {
        self.connectivity()
            .node_edge_count_direction(node, direction)
    }

    /// Iterator over the edges that are connected to a node.
    ///
    /// See [`Connectivity::node_edges`].
    pub fn node_edges(&self, n: NI, direction: Direction) -> Ct::NodeEdgesIterator<'_> {
        self.connectivity().node_edges(n, direction)
    }

    /// Iterate over connected nodes.
    ///
    /// See [`Connectivity::neighbours`].
    pub fn neighbours(&self, n: NI, direction: Direction) -> Ct::NeighboursIterator<'_> {
        self.connectivity().neighbours(n, direction)
    }

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    ///
    /// See [`Connectivity::edge_endpoint`].
    pub fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, PI)> {
        self.connectivity().edge_endpoint(e, direction)
    }

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// Returns the index of the port that was connected.
    ///
    /// See [`Connectivity::connect`].
    pub fn connect_first(
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
    pub fn connect_last(
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
    pub fn connect_at(
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
    pub fn disconnect(&mut self, edge_index: EI, direction: Direction) {
        self.connectivity_mut().disconnect(edge_index, direction)
    }
}

impl<N, E, P, NI, EI, PI, Ac, Ct, Ws> Graph<N, E, P, NI, EI, PI, Ac, Ct, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
    Ws: Weights<N, E, P, NI, EI, PI>,
{
    /// Returns a reference to the weights component.
    pub fn weights(&self) -> &Ws {
        &self.weights
    }
    /// Returns a mutable reference to the weights component.
    pub fn weights_mut(&mut self) -> &mut Ws {
        &mut self.weights
    }

    /// A reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight`].
    pub fn node_weight(&self, a: NI) -> Option<&N> {
        self.weights().node_weight(a)
    }

    /// A mutable reference to the weight of the node with a given index.
    ///
    /// See [`Weights::node_weight_mut`].
    pub fn node_weight_mut(&mut self, a: NI) -> Option<&mut N> {
        self.weights_mut().node_weight_mut(a)
    }

    /// Iterator over the node weights of the graph.
    ///
    /// See [`Weights::node_weights`].
    pub fn node_weights(&self) -> Ws::NodeWeightsIterator<'_> {
        self.weights().node_weights()
    }

    /// A reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight`].
    pub fn edge_weight(&self, e: EI) -> Option<&E> {
        self.weights().edge_weight(e)
    }

    /// A mutable reference to the weight of the edge with a given index.
    ///
    /// See [`Weights::edge_weight_mut`].
    pub fn edge_weight_mut(&mut self, e: EI) -> Option<&mut E> {
        self.weights_mut().edge_weight_mut(e)
    }

    /// Iterator over the edge weights of the graph.
    ///
    /// See [`Weights::edge_weights`].
    pub fn edge_weights(&self) -> Ws::EdgeWeightsIterator<'_> {
        self.weights().edge_weights()
    }

    /// A reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight`].
    pub fn port_weight(&self, e: PI) -> Option<&P> {
        self.weights().port_weight(e.clone())
    }

    /// A mutable reference to the weight of the port with a given index.
    ///
    /// See [`Weights::port_weight_mut`].
    pub fn port_weight_mut(&mut self, e: PI) -> Option<&mut P> {
        self.weights_mut().port_weight_mut(e)
    }

    /// Iterator over the port weights of the graph.
    ///
    /// See [`Weights::port_weights`].
    pub fn port_weights(&self) -> Ws::PortWeightsIterator<'_> {
        self.weights().port_weights()
    }
}

impl<N, E, P, NI, EI, PI, Ac, Ct, Ws> Graph<N, E, P, NI, EI, PI, Ac, Ct, Ws>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
    Ac: Allocator<NI, EI>,
    Ct: Connectivity<NI, EI, PI>,
    Ws: Weights<N, E, P, NI, EI, PI>,
{
    /// Create a new graph with no nodes or edges.
    pub fn new() -> Self {
        Self {
            allocator: Ac::new(),
            connectivity: Ct::new(),
            weights: Ws::new(),
            PhantomData,
        }
    }

    /// Create a new graph pre-allocating space for the given number of nodes and edges.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            allocator: Ac::with_capacity(nodes, edges),
            connectivity: Ct::with_capacity(nodes, edges),
            weights: Ws::with_capacity(nodes, edges),
            PhantomData,
        }
    }

    /// Add a new node to the graph and return its index.
    pub fn add_node(&mut self, weight: N) -> NI {
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
    pub fn add_node_with_edges(
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
    pub fn add_edge(&mut self, weight: E) -> EI {
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
    pub fn remove_node(&mut self, index: NI) -> Option<N> {
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
    pub fn remove_edge(&mut self, index: EI) -> Option<E> {
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
    pub fn insert_graph(&mut self, other: &Self) -> (NodeMap<NI>, EdgeMap<EI>) {
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
    pub fn compact(&mut self) -> (NodeMap<NI>, EdgeMap<EI>) {
        let (node_map, edge_map) = self.allocator_mut().compact();
        self.connectivity_mut().reindex(&node_map, &edge_map);
        self.weights_mut().reindex(&node_map, &edge_map);
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
            self.connect_at(from_node, into, Direction::Outgoing, from_port);
        }

        Ok(self.remove_edge(from).unwrap())
    }
}