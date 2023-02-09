use std::{collections::BTreeMap, marker::PhantomData};

use crate::{memory::EntityIndex, make_entity};

use super::{
    ConnectError, Direction
};

make_entity! {
    pub struct NodeIndex(u32);
    pub struct RegionIndex(u32);
    pub struct EdgeIndex(u32);
    pub struct PortIndex(u32);
}

/// Map of updated node indices after a graph operation.
pub type NodeMap<NI> = BTreeMap<NI, NI>;

/// Map of updated edge indices after a graph operation.
pub type EdgeMap<EI> = BTreeMap<EI, EI>;

pub struct DefaultAllocator<NI, EI> {
    nodes: Vec<NI>,
    edges: Vec<EI>,
}

pub struct DefaultConnectivity<NI, EI, PI> {
    nodes: Vec<Vec<(EI, Direction, PI)>>,
    edges: Vec<(NI, NI)>,
}

pub struct DefaultWeights<N, E, P, NI, EI, PI>(PhantomData<(N, E, P, NI, EI, PI)>);

/// Core trait defining the capability of allocating new nodes and edges.
/// All graph implementations must implement this trait.
pub trait Allocator<NI = NodeIndex, EI = EdgeIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    /// Iterator over the indices of all nodes in the graph.
    type NodeIndicesIterator<'a>: Iterator<Item = NI>
    where
        Self: 'a;

    /// Iterator over the indices of all edges in the graph.
    type EdgeIndicesIterator<'a>: Iterator<Item = EI>
    where
        Self: 'a;

    /// Create a new component with no nodes or edges.
    fn new() -> Self;

    /// Create a new component pre-allocating space for the given number of nodes and edges.
    fn with_capacity(nodes: usize, edges: usize) -> Self;

    /// Add a new node to the graph and return its index.
    fn new_node(&mut self) -> NI;

    /// Add a new edge to the graph and return its index.
    fn new_edge(&mut self) -> EI;

    /// Remove a node from the graph.
    fn remove_node(&mut self, node: NI);

    /// Remove an edge from the graph.
    fn remove_edge(&mut self, edge: EI);

    /// Returns a bound on the registered node indices.
    /// Any node index higher to this bound is currently invalid.
    fn node_bound(&self) -> NI;

    /// Returns a bound on the registered edge indices.
    /// Any edge index higher to this bound is currently invalid.
    fn edge_bound(&self) -> EI;

    /// Insert the elements of another allocator into this allocator.
    ///
    /// Returns maps from the node and edge indices in the original graph to the
    /// new indices which were allocated in this graph.
    fn insert_graph(&mut self, other: &Self) -> (NodeMap<NI>, EdgeMap<EI>);

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
    fn compact(&mut self) -> (NodeMap<NI>, EdgeMap<EI>);

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [`Allocator::compact`] before to make indices contiguous.
    fn shrink_to_fit(&mut self);

    // ---------------

    /// Returns the number of nodes in the graph.
    fn node_count(&self) -> usize;

    /// Returns the number of edges in the graph.
    fn edge_count(&self) -> usize;

    /// Check whether the graph has a node with a given index.
    fn has_node(&self, n: NI) -> bool;

    /// Check whether the graph has an edge with a given index.
    fn has_edge(&self, e: EI) -> bool;

    /// Whether the graph has neither nodes nor edges.
    #[inline]
    fn is_empty(&self) -> bool {
        self.node_count() == 0 && self.edge_count() == 0
    }

    /// Iterator over the node indices of the graph.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, Allocator};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let n0 = graph.add_node();
    /// let n1 = graph.add_node();
    /// let n2 = graph.add_node();
    ///
    /// graph.remove_node(n1);
    ///
    /// assert!(graph.node_indices().eq([n0, n2]));
    /// ```
    fn node_indices<'a>(&'a self) -> Self::NodeIndicesIterator<'a>;

    /// Iterator over the edge indices of the graph.
    fn edge_indices<'a>(&'a self) -> Self::EdgeIndicesIterator<'a>;
}

/// Trait for graphs that encode edges connecting nodes.
pub trait Connectivity<NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
{
    /// Iterator over the indices of the nodes connected to the given node.
    type NeighboursIterator<'a>: Iterator<Item = NI>
    where
        Self: 'a;
    /// Iterator over the indices of the edges connected to the given node.
    type NodeEdgesIterator<'a>: Iterator<Item = EI>
    where
        Self: 'a;

    /// Create a new component with no nodes or edges.
    fn new() -> Self;

    /// Create a new component pre-allocating space for the given number of nodes and edges.
    fn with_capacity(nodes: usize, edges: usize) -> Self;

    /// Registers a new node index in the internal data structures.
    fn register_node(&mut self, index: NI);

    /// Registers a new edge index in the internal data structures.
    fn register_edge(&mut self, index: EI);

    /// Remove a node from the internal data structures.
    fn unregister_node(&mut self, index: NI);

    /// Remove an edge from the internal data structures.
    fn unregister_edge(&mut self, index: EI);

    /// Insert the elements of another connectivity into this connectivity.
    fn insert_graph(&mut self, other: &Self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Reindex the nodes and edges.
    fn reindex(&mut self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Shrinks the graph's data store.
    fn shrink_to(&mut self, nodes: NI, edges: EI);

    // ---------------

    /// Returns the number of edges connected to the given node.
    fn node_edge_count(&self, node: NI) -> usize;

    /// Returns the number of edges connected to the given node in the given direction.
    fn node_edge_count_direction(&self, node: NI, direction: Direction) -> usize;

    /// Iterator over the edges that are connected to a node.
    fn node_edges<'a>(&'a self, n: NI, direction: Direction) -> Self::NodeEdgesIterator<'a>;

    /// Iterate over connected nodes.
    fn neighbours<'a>(&'a self, n: NI, direction: Direction) -> Self::NeighboursIterator<'a>;

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, PI)>;

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected before all other edges adjacent to the node.
    ///
    /// Returns the index of the port that was connected.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_unweighted();
    ///
    /// graph.connect_first(n0, e2, Direction::Incoming).unwrap();
    /// graph.connect_first(n0, e1, Direction::Incoming).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    /// ```
    fn connect_first(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<PI, ConnectError>;

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected after all other edges adjacent to the node.
    ///
    /// Returns the index of the port that was connected.
    fn connect_last(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
    ) -> Result<PI, ConnectError>;

    /// Connect edge to node, inserting to connection list at specified index.
    ///
    /// This operation takes time linear in index.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([e1], []).unwrap();
    ///
    /// graph.connect_at(n0, e2, Direction::Incoming, 1);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    ///
    /// ```
    fn connect_at(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        port: PI,
    ) -> Result<(), ConnectError>;

    /// Disconnect an edge endpoint from a node.
    ///
    /// This operation takes time linear in the number of edges that precede the edge to be
    /// disconnected at the node.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let e3 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([e1, e2, e3], []).unwrap();
    ///
    /// graph.disconnect(e2, Direction::Incoming);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e3]));
    ///
    /// graph.disconnect(e1, Direction::Incoming);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e3]));
    /// ```
    fn disconnect(&mut self, edge_index: EI, direction: Direction);
}

/// Trait for graphs that encode edges connecting nodes.
pub trait Weights<N, E, P, NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
{
    type NodeWeightsIterator<'a>: Iterator<Item = (NI, &'a N)>
    where
        Self: 'a,
        N: 'a;
    type EdgeWeightsIterator<'a>: Iterator<Item = (EI, &'a E)>
    where
        Self: 'a,
        E: 'a;
    type PortWeightsIterator<'a>: Iterator<Item = (PI, &'a P)>
    where
        Self: 'a,
        P: 'a;

    /// Create a new component with no nodes or edges.
    fn new() -> Self;

    /// Create a new component pre-allocating space for the given number of nodes and edges.
    fn with_capacity(nodes: usize, edges: usize) -> Self;

    /// Registers a new node index in the internal data structures.
    fn register_node(&mut self, index: NI, node: N);

    /// Registers a new edge index in the internal data structures.
    fn register_edge(&mut self, index: EI, edge: E);

    /// Remove a node from the internal data structures, returning its value.
    fn unregister_node(&mut self, index: NI) -> Option<N>;

    /// Remove an edge from the internal data structures, returning its value.
    fn unregister_edge(&mut self, index: EI) -> Option<E>;

    /// Insert the elements of another connectivity into this connectivity.
    fn insert_graph(&mut self, other: &Self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Reindex the nodes and edges.
    fn reindex(&mut self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Shrinks the graph's data store.
    fn shrink_to(&mut self, nodes: NI, edges: EI);

    // ---------------

    /// A reference to the weight of the node with a given index.
    fn node_weight(&self, a: NI) -> Option<&N>;

    /// A mutable reference to the weight of the node with a given index.
    fn node_weight_mut(&mut self, a: NI) -> Option<&mut N>;

    /// Iterator over the node weights of the graph.
    fn node_weights<'a>(&'a self) -> Self::NodeWeightsIterator<'a>;

    /// A reference to the weight of the edge with a given index.
    fn edge_weight(&self, e: EI) -> Option<&E>;

    /// A mutable reference to the weight of the edge with a given index.
    fn edge_weight_mut(&mut self, e: EI) -> Option<&mut E>;

    /// Iterator over the edge weights of the graph.
    fn edge_weights<'a>(&'a self) -> Self::EdgeWeightsIterator<'a>;

    /// A reference to the weight of the port with a given index.
    fn port_weight(&self, e: PI) -> Option<&P>;

    /// A mutable reference to the weight of the port with a given index.
    fn port_weight_mut(&mut self, e: PI) -> Option<&mut P>;

    /// Iterator over the port weights of the graph.
    fn port_weights<'a>(&'a self) -> Self::PortWeightsIterator<'a>;
}
