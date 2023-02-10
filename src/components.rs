use std::iter::Empty;
use std::marker::PhantomData;

use crate::index::slab::SlabIndexPool;
use crate::index::{slab, IndexPool, IndexPoolAlloc, IndexPoolIter};
use crate::memory::{self, EntityIndex};

use crate::memory::map::SecondaryMap;
use crate::{Direction, EdgeIndex, NodeIndex};

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

    /// Returns a bound on the number of registered node indices.
    /// Any node index higher or equal to this bound is currently invalid.
    fn node_bound(&self) -> usize;

    /// Returns a bound on the number of registered edge indices.
    /// Any edge index higher or equal to this bound is currently invalid.
    fn edge_bound(&self) -> usize;

    /// Insert the elements of another allocator into this one.
    ///
    /// Calls `rename_node` and `rename_edge` for each index in `other`, passing the new index as
    /// second argument.
    fn insert_from(
        &mut self,
        other: &Self,
        rename_node: impl FnMut(NI, NI),
        rename_edge: impl FnMut(EI, EI),
    );

    /// Reindex the nodes and edges to be contiguous.
    ///
    /// Calls `rename_node` and `rename_edge` for each index, passing the new index as
    /// second argument.
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
    fn compact(&mut self, rename_node: impl FnMut(NI, NI), rename_edge: impl FnMut(EI, EI));

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
pub trait Weights<N, E, P, NI = NodeIndex, EI = EdgeIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    type NodeWeights<'a>: Iterator<Item = (NI, &'a N)>
    where
        Self: 'a,
        N: 'a;
    type EdgeWeights<'a>: Iterator<Item = (EI, &'a E)>
    where
        Self: 'a,
        E: 'a;
    type PortWeights<'a>: Iterator<Item = (usize, &'a P)>
    where
        Self: 'a,
        P: 'a;

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
    fn port_weight(&self, p: usize, dir: Direction) -> Option<&P>;

    /// A mutable reference to the weight of the port with a given index.
    fn port_weight_mut(&mut self, p: usize, dir: Direction) -> Option<&mut P>;

    /// Iterator over the port weights of the graph.
    fn port_weights<'a>(&'a self, dir: Direction) -> Self::PortWeights<'a>;
}

/// Component which does not manage its own indices.
///
/// Indices of nodes and edges are not maintained by the structure; instead
/// every index value points to a node or edge which is not connected. These
/// components are intended to be used by some other structure like [`Slab`]
/// which keeps track of which indices are valid.
pub trait UnmanagedComponent<NI, EI>: Default {
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

    /// Shrinks the graph's data store.
    fn shrink_to(&mut self, nodes: usize, edges: usize);

    /// Insert the elements of another adjacency into this adjacency.
    fn insert_from(
        &mut self,
        other: &Self,
        node_map: impl FnMut(NI) -> NI,
        edge_map: impl FnMut(EI) -> EI,
    );

    /// Changes the key of a node.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    fn rekey_node(&mut self, old: NI, new: NI);

    /// Changes the key of an edge.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    fn rekey_edge(&mut self, old: EI, new: EI);

    // TODO: Capacity functions
}

// TODO: Remove this stub definitions once we have a good default allocator and weights

#[derive(Debug, Clone)]
pub struct DefaultAllocator<NI, EI> {
    nodes: SlabIndexPool<NI, ()>,
    edges: SlabIndexPool<EI, ()>,
}

impl<NI, EI> Default for DefaultAllocator<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn default() -> Self {
        Self {
            nodes: SlabIndexPool::new(),
            edges: SlabIndexPool::new(),
        }
    }
}

impl<NI, EI> Allocator<NI, EI> for DefaultAllocator<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    type NodeIndices<'a> = slab::IndexIter<'a, NI, ()>
    where
        Self: 'a;

    type EdgeIndices<'a> = slab::IndexIter<'a, EI, ()>
    where
        Self: 'a;

    fn new() -> Self {
        Default::default()
    }

    fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: SlabIndexPool::with_capacity(nodes),
            edges: SlabIndexPool::with_capacity(edges),
        }
    }

    fn new_node(&mut self) -> NI {
        self.nodes.allocate(()).unwrap()
    }

    fn new_edge(&mut self) -> EI {
        self.edges.allocate(()).unwrap()
    }

    fn remove_node(&mut self, node: NI) {
        self.nodes.free(node);
    }

    fn remove_edge(&mut self, edge: EI) {
        self.edges.free(edge);
    }

    fn node_bound(&self) -> usize {
        self.nodes.capacity()
    }

    fn edge_bound(&self) -> usize {
        self.edges.capacity()
    }

    fn insert_from(
        &mut self,
        other: &Self,
        mut rename_node: impl FnMut(NI, NI),
        mut rename_edge: impl FnMut(EI, EI),
    ) {
        for old in other.nodes.indices() {
            let new = self.new_node();
            rename_node(old, new);
        }
        for old in other.edges.indices() {
            let new = self.new_edge();
            rename_edge(old, new);
        }
    }

    fn compact(
        &mut self,
        mut rename_node: impl FnMut(NI, NI),
        mut rename_edge: impl FnMut(EI, EI),
    ) {
        self.nodes.compact(|_, old, new| rename_node(old, new));
        self.edges.compact(|_, old, new| rename_edge(old, new));
    }

    fn shrink_to_fit(&mut self) {
        self.nodes.shrink_to_fit();
        self.edges.shrink_to_fit();
    }

    fn node_count(&self) -> usize {
        self.nodes.len()
    }

    fn edge_count(&self) -> usize {
        self.edges.len()
    }

    fn has_node(&self, n: NI) -> bool {
        self.nodes.contains(n)
    }

    fn has_edge(&self, e: EI) -> bool {
        self.edges.contains(e)
    }

    fn node_indices<'a>(&'a self) -> Self::NodeIndices<'a> {
        self.nodes.indices()
    }

    fn edge_indices<'a>(&'a self) -> Self::EdgeIndices<'a> {
        self.edges.indices()
    }
}

#[derive(Debug, Clone)]
pub struct DefaultWeights<N, E, P, NI, EI> {
    nodes: SecondaryMap<NI, N>,
    edges: SecondaryMap<EI, E>,
    phantom_data: PhantomData<P>,
}

impl<N, E, P, NI, EI> Default for DefaultWeights<N, E, P, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
    N: Default,
    E: Default,
{
    fn default() -> Self {
        Self {
            nodes: SecondaryMap::new(),
            edges: SecondaryMap::new(),
            phantom_data: PhantomData,
        }
    }
}

impl<N, E, P, NI, EI> Weights<N, E, P, NI, EI> for DefaultWeights<N, E, P, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
    N: Clone,
    E: Clone,
{
    type NodeWeights<'a> = memory::map::Iter<'a, NI, N> where Self: 'a, N: 'a;
    type EdgeWeights<'a> = memory::map::Iter<'a, EI, E> where Self: 'a, E: 'a;
    type PortWeights<'a> = Empty<(usize, &'a P)> where Self: 'a, P: 'a;

    fn node_weight(&self, a: NI) -> Option<&N> {
        self.nodes.get(a)
    }

    fn node_weight_mut(&mut self, a: NI) -> Option<&mut N> {
        self.nodes.get_mut(a)
    }

    fn node_weights<'a>(&'a self) -> Self::NodeWeights<'a> {
        self.nodes.iter()
    }

    fn edge_weight(&self, e: EI) -> Option<&E> {
        self.edges.get(e)
    }

    fn edge_weight_mut(&mut self, e: EI) -> Option<&mut E> {
        self.edges.get_mut(e)
    }

    fn edge_weights<'a>(&'a self) -> Self::EdgeWeights<'a> {
        self.edges.iter()
    }

    fn port_weight(&self, _p: usize, _dir: Direction) -> Option<&P> {
        None
    }

    fn port_weight_mut(&mut self, _p: usize, _dir: Direction) -> Option<&mut P> {
        None
    }

    fn port_weights<'a>(&'a self, _dir: Direction) -> Self::PortWeights<'a> {
        Default::default()
    }
}

impl<N, E, P, NI, EI> UnmanagedComponent<NI, EI> for DefaultWeights<N, E, P, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
    N: Default,
    E: Default,
    P: Default,
    N: Clone,
    E: Clone,
{
    fn new() -> Self {
        Self {
            nodes: Default::default(),
            edges: Default::default(),
            phantom_data: PhantomData,
        }
    }

    fn with_capacity(nodes: usize, edges: usize) -> Self {
        Self {
            nodes: SecondaryMap::with_capacity(nodes),
            edges: SecondaryMap::with_capacity(edges),
            phantom_data: PhantomData,
        }
    }

    fn register_node(&mut self, index: NI) {
        if self.nodes.len() <= index.index() {
            self.nodes.resize(index.index() + 1);
        }
    }

    fn register_edge(&mut self, index: EI) {
        if self.edges.len() <= index.index() {
            self.edges.resize(index.index() + 1);
        }
    }

    fn unregister_node(&mut self, _index: NI) {}

    fn unregister_edge(&mut self, _index: EI) {}

    fn shrink_to(&mut self, nodes: usize, edges: usize) {
        self.nodes.resize(nodes);
        self.edges.resize(nodes);
    }

    fn insert_from(
        &mut self,
        other: &Self,
        mut node_map: impl FnMut(NI) -> NI,
        mut edge_map: impl FnMut(EI) -> EI,
    ) {
        for (old, n) in other.nodes.iter() {
            let new = node_map(old);
            self.register_node(new);
            self.nodes[new] = n.clone();
        }
        for (old, e) in other.edges.iter() {
            let new = edge_map(old);
            self.register_edge(new);
            self.edges[new] = e.clone();
        }
    }

    fn rekey_node(&mut self, old: NI, new: NI) {
        self.nodes.rekey(old, new);
    }

    fn rekey_edge(&mut self, old: EI, new: EI) {
        self.edges.rekey(old, new);
    }
}
