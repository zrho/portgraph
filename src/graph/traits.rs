use std::collections::BTreeMap;

use crate::{forest::LinkedForest, memory::EntityIndex};
pub use super::{Direction, EdgeIndex, NodeIndex, PortIndex, ConnectError, MergeEdgesError};

/// Map of updated node indices after a graph operation.
pub type NodeMap = BTreeMap<NodeIndex, NodeIndex>;

/// Map of updated edge indices after a graph operation.
pub type EdgeMap = BTreeMap<EdgeIndex, EdgeIndex>;

/// Core trait for directed graphs. Exposes unweighted nodes with edge ports.
///
/// The parameters `NI`, `EI`, and `PI` are respectively the node, edge and port index types.
pub trait BasePortGraph<NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
    PI: EntityIndex,
{
    type NodeIndicesIterator<'a>: Iterator<Item = NI>
    where
        Self: 'a;
    type NeighboursIterator<'a>: Iterator<Item = NI>
    where
        Self: 'a;
    type NodeEdgesIterator<'a>: Iterator<Item = EI>
    where
        Self: 'a;
    type EdgeIndicesIterator<'a>: Iterator<Item = EI>
    where
        Self: 'a;

    /// Create a new graph with no nodes or edges.
    fn new() -> Self;

    /// Create a new graph pre-allocating space for the given number of nodes, edges, and ports.
    fn with_capacity(nodes: usize, edges: usize, ports: usize) -> Self;

    /// Add a new node to the graph and return its index.
    fn add_node_unweighted(&mut self) -> NI;

    /// Returns the index at which the next node will be inserted.
    fn next_node_index(&self) -> NI;

    /// Add a node to the graph with specified incoming and outgoing edges.
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
    /// let n0 = graph.add_node_with_edges_unweighted([e1, e2], [e3]).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e3]));
    /// ```
    fn add_node_with_edges_unweighted(
        &mut self,
        incoming: impl IntoIterator<Item = EI>,
        outgoing: impl IntoIterator<Item = EI>,
    ) -> Result<NI, ConnectError>;

    /// Add a new disconnected edge to the graph and return its index.
    fn add_edge_unweighted(&mut self) -> EI;

    /// Remove a node from the graph.
    ///
    /// The edges connected to the node will remain in the graph but will become dangling.
    ///
    /// Returns the node's weight if it existed or `None` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([e1], []).unwrap();
    ///
    /// assert_eq!(graph.remove_node_unweighted(n0), true);
    /// assert_eq!(graph.remove_node_unweighted(n0), false);
    /// assert!(graph.has_edge(e1));
    /// assert_eq!(graph.edge_endpoint(e1, Direction::Incoming), None);
    /// ```
    fn remove_node_unweighted(&mut self, node_index: NI) -> bool;

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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let e3 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([e1, e2, e3], []).unwrap();
    ///
    /// assert_eq!(graph.remove_edge_unweighted(e2), true);
    /// assert_eq!(graph.remove_edge_unweighted(e2), false);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e3]));
    /// ```
    fn remove_edge_unweighted(&mut self, e: EI) -> bool;

    /// Check whether the graph has a node with a given index.
    fn has_node(&self, n: NI) -> bool;

    /// Check whether the graph has an edge with a given index.
    fn has_edge(&self, e: EI) -> bool;

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected after the edge with index `edge_prev`.
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
    /// let n0 = graph.add_node_with_edges_unweighted([e1, e3], []).unwrap();
    ///
    /// graph.connect_after(n0, e2, Direction::Incoming, e1).unwrap();
    ///
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2, e3]));
    /// ```
    fn connect_after(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        edge_prev: EI,
    ) -> Result<(), ConnectError>;

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected before all other edges adjacent to the node.
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
    ) -> Result<(), ConnectError>;

    /// Connect an edge to an incoming or outgoing port of a node.
    fn connect(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        edge_prev: Option<EI>,
    ) -> Result<(), ConnectError>;

    /// Connect a collection of edges to incoming or outgoing ports of a node.
    fn connect_many(
        &mut self,
        node: NI,
        edges: impl IntoIterator<Item = EI>,
        direction: Direction,
        edge_prev: Option<EI>,
    ) -> Result<(), ConnectError>;

    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// The edge will be connected after all other edges adjacent to the node.
    fn connect_last(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
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

    ///
    fn replace_connection(
        &mut self,
        prev: EI,
        new: EI,
        direction: Direction,
    ) -> Result<(), ConnectError>;

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
    /// graph.insert_edge(n0, e2, Direction::Incoming, 1);
    /// assert!(graph.node_edges(n0, Direction::Incoming).eq([e1, e2]));
    ///
    /// ```
    fn insert_edge(
        &mut self,
        node: NI,
        edge: EI,
        direction: Direction,
        index: usize,
    ) -> Result<(), ConnectError>;

    /// The endpoint of an edge in a given direction.
    ///
    /// Returns `None` if the edge does not exist or has no endpoint in that direction.
    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<NI>;

    /// Iterator over the edges that are connected to a node.
    fn node_edges<'a>(&'a self, n: NI, direction: Direction) -> Self::NodeEdgesIterator<'a>;

    // Iterate over connected nodes.
    fn neighbours<'a>(&'a self, n: NI, direction: Direction) -> Self::NeighboursIterator<'a>;

    /// Iterator over the node indices of the graph.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let n0 = graph.add_node_unweighted();
    /// let n1 = graph.add_node_unweighted();
    /// let n2 = graph.add_node_unweighted();
    ///
    /// graph.remove_node_unweighted(n1);
    ///
    /// assert!(graph.node_indices().eq([n0, n2]));
    /// ```
    fn node_indices<'a>(&'a self) -> Self::NodeIndicesIterator<'a>;

    fn edge_indices<'a>(&'a self) -> Self::EdgeIndicesIterator<'a>;

    /// Number of nodes in the graph.
    fn node_count(&self) -> usize;

    /// Number of edges in the graph.
    fn edge_count(&self) -> usize;

    /// Number of ports in the graph.
    fn port_count(&self) -> usize;

    /// Whether the graph has neither nodes nor edges.
    #[inline]
    fn is_empty(&self) -> bool {
        self.node_count() == 0 && self.edge_count() == 0
    }

    /// Insert a graph into this graph.
    ///
    /// Returns maps from the node and edge indices in the original graph to the
    /// new indices which were allocated in this graph.
    ///
    /// [Graph::merge_edges] can be used along dangling edges to connect the inserted
    /// subgraph with the rest of the graph
    fn insert_graph(&mut self, other: Self) -> (NodeMap, EdgeMap);

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
    fn compact(&mut self) -> (NodeMap, EdgeMap);

    /// Shrinks the graph's data store as much as possible.
    ///
    /// When there are a lot of empty slots, call [Graph::compact] before to make indices contiguous.
    fn shrink_to_fit(&mut self);

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
    /// # use portgraph::graph::{Graph, Direction, BasePortGraph};
    /// let mut graph = Graph::<(), ()>::new();
    ///
    /// let e1 = graph.add_edge_unweighted();
    /// let e2 = graph.add_edge_unweighted();
    /// let n0 = graph.add_node_with_edges_unweighted([], [e1]).unwrap();
    /// let n1 = graph.add_node_with_edges_unweighted([e2], []).unwrap();
    ///
    /// assert_eq!(graph.merge_edges_unweighted(e2, e1).unwrap(), ());
    /// assert!(!graph.has_edge(e2));
    /// assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1]));
    /// assert!(graph.node_edges(n1, Direction::Incoming).eq([e1]));
    /// ```
    fn merge_edges_unweighted(&mut self, from: EI, into: EI) -> Result<(), MergeEdgesError>;

    /// Returns the index of the previous edge that is connected to the node in the given direction.
    fn edge_prev(&self, edge_index: EI, direction: Direction) -> Option<EI>;
}

pub trait WeightedPortGraph<N, E = (), P = (), NI = NodeIndex, EI = EdgeIndex, PI = PortIndex>:
    BasePortGraph<NI, EI, PI>
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

    /// Add a new node to the graph and return its index.
    fn add_node(&mut self, weight: N) -> NI;

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
    ) -> Result<NI, ConnectError>;

    /// Add an edge to the graph.
    fn add_edge(&mut self, weight: E) -> EI;

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
    ///
    /// TODO: May be a good idea to choose a different name that doesn't conflict with the method in `BasePortGraph`.
    fn remove_node(&mut self, node_index: NI) -> Option<N>;

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
    fn remove_edge(&mut self, e: EI) -> Option<E>;

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
    fn merge_edges(&mut self, from: EI, into: EI) -> Result<E, MergeEdgesError>;
}

/// Access the node layout of a graph.
pub trait IntoLayout<NI : EntityIndex = NodeIndex> {
    /// Get a reference to the node layout of the graph.
    fn layout(&self) -> &LinkedForest<NI>;

    /// Get a mutable reference to the node layout of the graph.
    fn layout_mut(&mut self) -> &mut LinkedForest<NI>;
}
