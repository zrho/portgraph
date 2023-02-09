use std::{collections::{BTreeMap, HashSet}, marker::PhantomData};

use crate::{memory::EntityIndex, make_entity, Insert};

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
    nodes: HashSet<NI>,
    edges: HashSet<EI>,
}

pub struct DefaultAdjacency<NI, EI, PI> {
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
    type NodeIndices<'a>: Iterator<Item = NI>
    where
        Self: 'a;

    /// Iterator over the indices of all edges in the graph.
    type EdgeIndices<'a>: Iterator<Item = EI>
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
    fn node_indices<'a>(&'a self) -> Self::NodeIndices<'a>;

    /// Iterator over the edge indices of the graph.
    fn edge_indices<'a>(&'a self) -> Self::EdgeIndices<'a>;
}

/// Trait for graphs that encode edges connecting nodes.
pub trait Adjacency<NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
{
    /// Iterator over the indices of the nodes connected to the given node.
    type Neighbours<'a>: Iterator<Item = NI>
    where
        Self: 'a;
    /// Iterator over the indices of the edges connected to the given node.
    type NodeEdges<'a>: Iterator<Item = EI>
    where
        Self: 'a;

    /// Iterator over the edges that are connected to a node.
    fn node_edges(& self, n: NI, direction: Direction) -> Self::NodeEdges<'_>;

    /// Returns the number of edges connected to the given node.
    #[inline(always)]
    fn node_edge_count(&self, node: NI) -> usize {
        self.node_edges(node, Direction::Incoming).count()
            + self.node_edges(node, Direction::Outgoing).count()
    }

    /// Shorthand for [`Graph::node_edges`] in the incoming direction.
    #[inline]
    fn inputs(&self, node: NI) -> Self::NodeEdges<'_> {
        self.node_edges(node, Direction::Incoming)
    }

    /// Shorthand for [`Graph::node_edges`] in the outgoing direction.
    #[inline]
    fn outputs(&self, node: NI) -> Self::NodeEdges<'_> {
        self.node_edges(node, Direction::Outgoing)
    }

    /// Iterate over connected nodes.
    fn neighbours(& self, n: NI, direction: Direction) -> Self::Neighbours<'_>;

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, PI)>;

    /// Shorthand for [`Graph::edge_endpoint`] in the outgoing direction.
    #[inline]
    fn source(&self, edge: EI) -> Option<(NI, PI)> {
        self.edge_endpoint(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_endpoint`] in the incoming direction.
    #[inline]
    fn target(&self, edge: EI) -> Option<(NI, PI)> {
        self.edge_endpoint(edge, Direction::Incoming)
    }

    /// Returns the node that the `edge` is connected to.
    ///
    /// `None` if the edge does not exist or is not connected in the direction.
    #[inline]
    fn edge_node(&self, edge: EI, dir: Direction) -> Option<NI> {
        self.edge_endpoint(edge, dir).map(|(node, _)| node)
    }

    /// Shorthand for [`Graph::edge_node`] in the outgoing direction.
    #[inline]
    fn source_node(&self, edge: EI) -> Option<NI> {
        self.edge_node(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_node`] in the incoming direction.
    #[inline]
    fn target_node(&self, edge: EI) -> Option<NI> {
        self.edge_node(edge, Direction::Incoming)
    }

    /// Returns the position in the node's edge list an `edge` is connected to.
    ///
    /// `None` if the edge does not exist or is not connected in the direction.
    #[inline]
    fn edge_position(&self, edge: EI, dir: Direction) -> Option<PI> {
        self.edge_endpoint(edge, dir).map(|(_, position)| position)
    }

    /// Shorthand for [`Graph::edge_position`] in the outgoing direction.
    #[inline]
    fn source_position(&self, edge: EI) -> Option<PI> {
        self.edge_position(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_position`] in the incoming direction.
    #[inline]
    fn target_position(&self, edge: EI) -> Option<PI> {
        self.edge_position(edge, Direction::Incoming)
    }
}

/// Trait for graphs that encode edges connecting nodes.
pub trait AdjacencyMut<NI = NodeIndex, EI = EdgeIndex, PI = PortIndex> : Adjacency<NI, EI, PI>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
{
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

    /// Insert the elements of another adjacency into this adjacency.
    fn insert_graph(&mut self, other: &Self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Reindex the nodes and edges.
    fn reindex(&mut self, node_map: &NodeMap<NI>, edge_map: &EdgeMap<EI>);

    /// Shrinks the graph's data store.
    fn shrink_to(&mut self, nodes: NI, edges: EI);

    // ---------------

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// # Errors
    ///
    ///  - When the edge is already connected.
    ///  - When trying to insert relative to an edge that is not connected to the same node.
    ///
    /// In the case of an error, the graph is unchanged.
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
    fn connect(
        &mut self,
        node: NI,
        edge: EI,
        position: Insert<EI>,
        direction: Direction,
    ) -> Result<(), ConnectError>;

    /// Extends the ports of `node`.
    ///
    /// # Errors
    ///
    ///  - When one of the edge is already connected.
    ///
    /// Connects edges until an error is discovered.
    fn connect_many<I>(
        &mut self,
        node: NI,
        edges: I,
        position: Insert<EI>,
        direction: Direction,
    ) -> Result<(), ConnectError>
    where
        I: IntoIterator<Item = EI>;

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
    type NodeWeights<'a>: Iterator<Item = (NI, &'a N)>
    where
        Self: 'a,
        N: 'a;
    type EdgeWeights<'a>: Iterator<Item = (EI, &'a E)>
    where
        Self: 'a,
        E: 'a;
    type PortWeights<'a>: Iterator<Item = (PI, &'a P)>
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

    /// Insert the elements of another weights into these weights.
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
    fn node_weights<'a>(&'a self) -> Self::NodeWeights<'a>;

    /// A reference to the weight of the edge with a given index.
    fn edge_weight(&self, e: EI) -> Option<&E>;

    /// A mutable reference to the weight of the edge with a given index.
    fn edge_weight_mut(&mut self, e: EI) -> Option<&mut E>;

    /// Iterator over the edge weights of the graph.
    fn edge_weights<'a>(&'a self) -> Self::EdgeWeights<'a>;

    /// A reference to the weight of the port with a given index.
    fn port_weight(&self, e: PI) -> Option<&P>;

    /// A mutable reference to the weight of the port with a given index.
    fn port_weight_mut(&mut self, e: PI) -> Option<&mut P>;

    /// Iterator over the port weights of the graph.
    fn port_weights<'a>(&'a self) -> Self::PortWeights<'a>;
}
