//! An undirected portgraph with hyperedges.
use crate::memory::EntityIndex;
use crate::memory::{list::EntityList, ListPool, Slab};
use crate::{EdgeIndex, NodeIndex, PortIndex};

/// An undirected portgraph with hyperedges.
///
/// This data structure consists of nodes, edges, and ports.
/// Every node has an ordered list of ports attached to it.
/// Edges can be connected to an arbitrary set of ports but any port admits at most one edge connection.
///
/// This portgraph is undirected in the sense that a node has only one list of ports which are only distinguished by their position.
/// Directed variants of the portgraph can be built on top of this data structure by partitioning the port list according to the direction in which edges would connect to a port.
#[derive(Debug, Clone)]
pub struct PortGraph<N, E, P> {
    nodes: Slab<NodeIndex, Node<N>>,
    edges: Slab<EdgeIndex, Edge<E>>,
    ports: Slab<PortIndex, Port<P>>,
    port_lists: ListPool<PortIndex>,
}

impl<N, E, P> PortGraph<N, E, P> {
    /// Creates a new empty graph.
    pub fn new() -> Self {
        Self {
            nodes: Slab::new(),
            edges: Slab::new(),
            ports: Slab::new(),
            port_lists: ListPool::new(),
        }
    }

    pub fn with_capacity(nodes: usize, edges: usize, ports: usize) -> Self {
        Self {
            nodes: Slab::with_capacity(nodes),
            edges: Slab::with_capacity(edges),
            ports: Slab::with_capacity(ports),
            port_lists: ListPool::with_capacity(ports * 4),
        }
    }

    /// Adds a new node to the graph with no ports.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<usize, (), ()>::new();
    /// let node = graph.add_node(7);
    /// assert_eq!(graph[node], 7);
    /// assert_eq!(graph.node_ports(node), []);
    /// ```
    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.nodes.insert(Node {
            weight,
            ports: EntityList::default(),
        })
    }

    /// Adds a new node to the graph with a specified list of ports.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<usize, (), usize>::new();
    /// let node = graph.add_node_with_ports(7, [1, 2, 3]);
    /// assert_eq!(graph[node], 7);
    /// assert_eq!(graph.node_ports(node).len(), 3);
    /// ```
    pub fn add_node_with_ports<I>(&mut self, weight: N, port_weights: I) -> NodeIndex
    where
        I: IntoIterator<Item = P>,
    {
        let node = self.add_node(weight);
        self.add_ports(node, port_weights);
        node
    }

    /// Adds a new edge to the graph.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), usize, ()>::new();
    /// let edge = graph.add_edge(3);
    /// assert_eq!(graph[edge], 3);
    /// ```
    pub fn add_edge(&mut self, weight: E) -> EdgeIndex {
        self.edges.insert(Edge {
            weight,
            ports: EntityList::default(),
        })
    }

    /// Adds a port to a node at the last position.
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), (), usize>::new();
    /// let node = graph.add_node(());
    /// let port0 = graph.add_port(node, 0);
    /// let port1 = graph.add_port(node, 1);
    /// let port2 = graph.add_port(node, 2);
    /// assert_eq!(graph.node_ports(node), [port0, port1, port2]);
    /// ```
    pub fn add_port(&mut self, node: NodeIndex, weight: P) -> PortIndex {
        let port_index = self.ports.insert(Port {
            weight,
            node,
            edge: None,
        });

        self.nodes[node]
            .ports
            .push(port_index, &mut self.port_lists);

        port_index
    }

    /// Swaps the ports at two positions in a node's port list.
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist or the indices are out of bounds.
    pub fn swap_ports(&mut self, node: NodeIndex, a: usize, b: usize) {
        let ports = &mut self.nodes[node].ports.slice_mut(&mut self.port_lists);
        ports.swap(a, b);
    }

    /// Sorts the ports of a node using a comparison function.
    ///
    /// This sort is stable.
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    pub fn sort_ports_by<F>(&mut self, node: NodeIndex, cmp: F)
    where
        F: Fn(&N, PortIndex, &P, PortIndex, &P) -> std::cmp::Ordering,
    {
        let node_data = &mut self.nodes[node];
        let ports = node_data.ports.slice_mut(&mut self.port_lists);
        ports.sort_by(|a, b| {
            cmp(
                &node_data.weight,
                *a,
                &self.ports[*a].weight,
                *b,
                &self.ports[*b].weight,
            )
        });
    }

    /// Sorts the ports of a node by a key.
    ///
    /// This sort is stable.
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    pub fn sort_ports_by_key<F, K>(&mut self, node: NodeIndex, mut key: F)
    where
        F: FnMut(&N, PortIndex, &P) -> K,
        K: Ord,
    {
        let node_data = &mut self.nodes[node];
        let ports = node_data.ports.slice_mut(&mut self.port_lists);
        ports.sort_by_key(|port| key(&node_data.weight, *port, &self.ports[*port].weight));
    }

    /// Adds a port to a node at an index within the node's list of ports.
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist or the `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), (), &'static str>::new();
    /// let node = graph.add_node(());
    /// let port0 = graph.add_port_at(node, 0, "foo");
    /// let port1 = graph.add_port_at(node, 0, "bar");
    /// let port2 = graph.add_port_at(node, 1, "baz");
    /// assert_eq!(graph.node_ports(node), [port1, port2, port0]);
    /// ```
    pub fn add_port_at(&mut self, node: NodeIndex, index: usize, weight: P) -> PortIndex {
        let port = self.ports.insert(Port {
            weight,
            node,
            edge: None,
        });

        self.nodes[node]
            .ports
            .insert(index, port, &mut self.port_lists);

        port
    }

    /// Adds a collection of ports to the end of a node's port list.
    ///
    /// Returns a range with the positions of the added ports in the node's port list.
    ///
    /// When the iterator over the collection has exact size bounds,
    /// this can be more efficient than repeated applications of [`add_port`].
    ///
    /// [`add_port`]: crate::undirected::PortGraph::add_port
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), (), &'static str>::new();
    /// let node = graph.add_node(());
    /// assert_eq!(graph.add_ports(node, ["foo", "bar"]), 0..2);
    /// assert_eq!(graph.add_ports(node, ["baz", "quux"]), 2..4);
    /// ```
    pub fn add_ports<I>(&mut self, node: NodeIndex, weights: I) -> std::ops::Range<usize>
    where
        I: IntoIterator<Item = P>,
    {
        // TODO: Check if node exists and panic before inserting anything
        let indices = self.ports.extend(weights.into_iter().map(|weight| Port {
            weight,
            node,
            edge: None,
        }));

        let num_ports_before = self.nodes[node].ports.len(&self.port_lists);
        self.nodes[node].ports.extend(indices, &mut self.port_lists);
        let num_ports_after = self.nodes[node].ports.len(&self.port_lists);
        num_ports_before..num_ports_after
    }

    /// Removes a port from the graph while preserving ordering the ordering of ports attached to the node.
    ///
    /// Returns the port's weight if the port existed.
    ///
    /// This operation is *O*(n) in the number of ports attached to the same node at later positions.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), (), usize>::new();
    /// let node = graph.add_node_with_ports((), [0, 1, 2]);
    /// let ports = graph.node_ports(node).to_vec();
    /// assert_eq!(graph.remove_port(ports[1]), Some(1));
    /// assert_eq!(graph.remove_port(ports[1]), None);
    /// assert_eq!(graph.node_ports(node), [ports[0], ports[2]]);
    /// ```
    pub fn remove_port(&mut self, port: PortIndex) -> Option<P> {
        let port_data = self.ports.remove(port)?;

        self.nodes[port_data.node].remove_port(port, &mut self.port_lists);

        if let Some(edge) = port_data.edge {
            self.edges[edge].swap_remove_port(port, &mut self.port_lists);
        }

        Some(port_data.weight)
    }

    // TODO: Test that `remove_port` and `swap_remove_port` disconnect the edge properly

    /// Removes a port from the graph by swapping positions with the last port attached to the node.
    ///
    /// Returns the port's weight if the port existed.
    ///
    /// This operation is *O*(1) but it does not preserve the ordering of the node ports.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), (), usize>::new();
    /// let node = graph.add_node_with_ports((), [0, 1, 2]);
    /// let ports = graph.node_ports(node).to_vec();
    /// assert_eq!(graph.swap_remove_port(ports[0]), Some(0));
    /// assert_eq!(graph.swap_remove_port(ports[0]), None);
    /// assert_eq!(graph.node_ports(node), [ports[2], ports[1]]);
    /// ```
    pub fn swap_remove_port(&mut self, port: PortIndex) -> Option<P> {
        let port_data = self.ports.remove(port)?;

        self.nodes[port_data.node].swap_remove_port(port, &mut self.port_lists);

        if let Some(edge) = port_data.edge {
            self.edges[edge].swap_remove_port(port, &mut self.port_lists);
        }

        Some(port_data.weight)
    }

    /// Removes a node from the graph, returning its weight if the node existed.
    ///
    /// This will also remove all the ports belonging to the node and drop their weights.
    ///
    /// This operation is *O*(n) in the number of ports attached to the node.
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<usize, usize, usize>::new();
    /// let node = graph.add_node(5);
    /// let port = graph.add_port(node, 2);
    /// let edge = graph.add_edge(8);
    /// graph.connect(port, edge);
    /// assert_eq!(graph.remove_node(node), Some(5));
    /// assert_eq!(graph.remove_node(node), None);
    /// assert!(!graph.contains_port(port));
    /// assert_eq!(graph.edge_ports(edge), []);
    /// ```
    pub fn remove_node(&mut self, node: NodeIndex) -> Option<N> {
        let mut node_data = self.nodes.remove(node)?;

        // When removing the node's ports we have to adjust the port lists of the edges they are connected to.
        // Iterating over the slice of the node's ports directly borrows the port list pool
        // but modifying an edge's port list needs to mutably borrow the port list pool as well.
        // Using indices into the node's port list we can avoid allocating.
        let port_count = node_data.ports.len(&self.port_lists);

        for i in 0..port_count {
            let port_index = node_data.ports.slice(&self.port_lists)[i];
            let port = self.ports.remove(port_index).unwrap();

            if let Some(edge) = port.edge {
                self.edges[edge].swap_remove_port(port_index, &mut self.port_lists);
            }
        }

        node_data.ports.clear(&mut self.port_lists);

        Some(node_data.weight)
    }

    /// Removes an edge from the graph, returning its weights if the edge existed.
    ///
    /// This will disconnect every port that the edge was connected to.
    ///
    /// ```
    /// # use portgraph::undirected::PortGraph;
    /// let mut graph = PortGraph::<(), usize, ()>::new();
    /// let node = graph.add_node(());
    /// let port = graph.add_port(node, ());
    /// let edge = graph.add_edge(5);
    /// graph.connect(port, edge);
    /// assert_eq!(graph.remove_edge(edge), Some(5));
    /// assert_eq!(graph.remove_edge(edge), None);
    /// assert!(graph.contains_port(port));
    /// assert_eq!(graph.port_edge(port), None);
    /// ```
    pub fn remove_edge(&mut self, edge: EdgeIndex) -> Option<E> {
        let mut edge_data = self.edges.remove(edge)?;

        for port_index in edge_data.ports.slice(&self.port_lists) {
            self.ports[*port_index].edge = None;
        }

        edge_data.ports.clear(&mut self.port_lists);

        Some(edge_data.weight)
    }

    /// Returns a slice containing the ports belonging to a node in order.
    ///
    /// When the node does not exist, this method returns an empty slice.
    pub fn node_ports(&self, node: NodeIndex) -> &[PortIndex] {
        match self.nodes.get(node) {
            Some(node_data) => node_data.ports.slice(&self.port_lists),
            None => &[],
        }
    }

    /// Returns a slice containing the ports that the edge is connected to in any order.
    ///
    /// When the edge does not exist, this method returns an empty slice.
    pub fn edge_ports(&self, edge: EdgeIndex) -> &[PortIndex] {
        match self.edges.get(edge) {
            Some(edge_data) => edge_data.ports.slice(&self.port_lists),
            None => &[],
        }
    }

    /// Returns the node that a port belongs to.
    ///
    /// # Panics
    ///
    /// Panics if the port does not exist.
    pub fn port_node(&self, port: PortIndex) -> NodeIndex {
        self.ports[port].node
    }

    /// Returns the edge that a port is connected to, if any.
    ///
    /// # Panics
    ///
    /// Panics if the port does not exist.
    pub fn port_edge(&self, port: PortIndex) -> Option<EdgeIndex> {
        self.ports[port].edge
    }

    /// Connect a port to an edge.
    ///
    /// A port can be connected to at most one edge at a time.
    /// If the port was previously connected to another edge, it will be disconnected from that edge.
    ///
    /// # Panics
    ///
    /// Panics if the edge or the port do not exist.
    pub fn connect(&mut self, port: PortIndex, edge: EdgeIndex) {
        let prev_edge = std::mem::replace(&mut self.ports[port].edge, Some(edge));

        if prev_edge == Some(edge) {
            return;
        }

        self.edges[edge].ports.push(port, &mut self.port_lists);

        if let Some(prev_edge) = prev_edge {
            self.edges[prev_edge].swap_remove_port(port, &mut self.port_lists);
        }
    }

    /// Disconnects a port from the edge it is connected to.
    ///
    /// Does nothing if the port is not connected.
    ///
    /// # Panics
    ///
    /// Panics if the port does not exist.
    pub fn disconnect(&mut self, port: PortIndex) {
        if let Some(edge) = std::mem::take(&mut self.ports[port].edge) {
            self.edges[edge].swap_remove_port(port, &mut self.port_lists);
        }
    }

    /// Returns whether this graph contains a node.
    pub fn contains_node(&self, node: NodeIndex) -> bool {
        self.nodes.contains(node)
    }

    /// Returns whether this graph contains an edge.
    pub fn contains_edge(&self, edge: EdgeIndex) -> bool {
        self.edges.contains(edge)
    }

    /// Returns whether this graph contains a port.
    pub fn contains_port(&self, port: PortIndex) -> bool {
        self.ports.contains(port)
    }

    /// Borrows the weight of a node if it exists.
    pub fn node_weight(&self, node: NodeIndex) -> Option<&N> {
        Some(&self.nodes.get(node)?.weight)
    }

    /// Mutably borrows the weight of a node if it exists.
    pub fn node_weight_mut(&mut self, node: NodeIndex) -> Option<&mut N> {
        Some(&mut self.nodes.get_mut(node)?.weight)
    }

    /// Borrows the weight of an edge if it exists.
    pub fn edge_weight(&self, edge: EdgeIndex) -> Option<&E> {
        Some(&self.edges.get(edge)?.weight)
    }

    /// Mutably borrows the weight of an edge if it exists.
    pub fn edge_weight_mut(&mut self, edge: EdgeIndex) -> Option<&mut E> {
        Some(&mut self.edges.get_mut(edge)?.weight)
    }

    /// Borrows the weight of a port if it exists.
    pub fn port_weight(&self, port: PortIndex) -> Option<&P> {
        Some(&self.ports.get(port)?.weight)
    }

    /// Mutably borrows the weight of a port if it exists.
    pub fn port_weight_mut(&mut self, port: PortIndex) -> Option<&mut P> {
        Some(&mut self.ports.get_mut(port)?.weight)
    }

    /// Returns the number of nodes.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Iterates over the nodes with indices and weights.
    pub fn nodes(&self) -> impl Iterator<Item = (NodeIndex, &N)> {
        self.nodes
            .iter()
            .map(|(index, node_data)| (index, &node_data.weight))
    }

    /// Iterates over the nodes with indices and mutable weights.
    pub fn nodes_mut(&mut self) -> impl Iterator<Item = (NodeIndex, &mut N)> {
        self.nodes
            .iter_mut()
            .map(|(index, node_data)| (index, &mut node_data.weight))
    }

    /// Returns the number of edges.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Iterates over the edges with indices and weights.
    pub fn edges(&self) -> impl Iterator<Item = (EdgeIndex, &E)> {
        self.edges
            .iter()
            .map(|(index, edge_data)| (index, &edge_data.weight))
    }

    /// Iterates over the edges with indices and mutable weights.
    pub fn edges_mut(&mut self) -> impl Iterator<Item = (EdgeIndex, &mut E)> {
        self.edges
            .iter_mut()
            .map(|(index, edge_data)| (index, &mut edge_data.weight))
    }

    /// Returns the number of ports.
    pub fn port_count(&self) -> usize {
        self.ports.len()
    }

    /// Iterates over the ports with indices and weights.
    pub fn ports(&self) -> impl Iterator<Item = (PortIndex, &P)> {
        self.ports
            .iter()
            .map(|(index, port_data)| (index, &port_data.weight))
    }

    /// Iterates over the ports with indices and mutable weights.
    pub fn ports_mut(&mut self) -> impl Iterator<Item = (PortIndex, &mut P)> {
        self.ports
            .iter_mut()
            .map(|(index, port_data)| (index, &mut port_data.weight))
    }

    /// Shrink the internal buffers to fit the current contents.
    pub fn shrink_to_fit(&mut self) {
        self.nodes.shrink_to_fit();
        self.edges.shrink_to_fit();
        self.ports.shrink_to_fit();
    }

    /// Compacts the internal data structures.
    ///
    /// The provided rekey functions are called with the weight, the old index and the new index of every part of the graph.
    /// The rekey functions are called for ports first, then for nodes and finally for edges.
    ///
    /// If one of the rekey functions panics, the data structure will be left in an inconsistent state.
    pub fn compact<FN, FE, FP>(
        &mut self,
        mut rekey_ports: FP,
        mut rekey_nodes: FN,
        mut rekey_edges: FE,
    ) where
        FN: FnMut(&mut N, NodeIndex, NodeIndex),
        FE: FnMut(&mut E, EdgeIndex, EdgeIndex),
        FP: FnMut(&mut P, PortIndex, PortIndex),
    {
        // TODO: Try to do this without allocation?
        let mut port_old_to_new = Vec::new();
        port_old_to_new.resize(self.ports.upper_bound().index(), PortIndex::new(0));

        self.ports.compact(|port_data, port_old, port_new| {
            rekey_ports(&mut port_data.weight, port_old, port_new);
            port_old_to_new[port_old.index()] = port_new;
        });

        self.nodes.compact(|node_data, node_old, node_new| {
            rekey_nodes(&mut node_data.weight, node_old, node_new);
            for port in node_data.ports.slice_mut(&mut self.port_lists) {
                *port = port_old_to_new[port.index()];
                self.ports[*port].node = node_new;
            }
        });

        self.edges.compact(|edge_data, edge_old, edge_new| {
            rekey_edges(&mut edge_data.weight, edge_old, edge_new);
            for port in edge_data.ports.slice_mut(&mut self.port_lists) {
                *port = port_old_to_new[port.index()];
                self.ports[*port].edge = Some(edge_new);
            }
        });

        // TODO compact the list pool as well
    }

    // TODO reserve
    // TODO with_capacity
    // TODO nicer debug representation
}

impl<N, E, P> Default for PortGraph<N, E, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N, E, P> std::ops::Index<NodeIndex> for PortGraph<N, E, P> {
    type Output = N;

    fn index(&self, index: NodeIndex) -> &Self::Output {
        self.node_weight(index).unwrap()
    }
}

impl<N, E, P> std::ops::IndexMut<NodeIndex> for PortGraph<N, E, P> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        self.node_weight_mut(index).unwrap()
    }
}

impl<N, E, P> std::ops::Index<PortIndex> for PortGraph<N, E, P> {
    type Output = P;

    fn index(&self, index: PortIndex) -> &Self::Output {
        self.port_weight(index).unwrap()
    }
}

impl<N, E, P> std::ops::IndexMut<PortIndex> for PortGraph<N, E, P> {
    fn index_mut(&mut self, index: PortIndex) -> &mut Self::Output {
        self.port_weight_mut(index).unwrap()
    }
}

impl<N, E, P> std::ops::Index<EdgeIndex> for PortGraph<N, E, P> {
    type Output = E;

    fn index(&self, index: EdgeIndex) -> &Self::Output {
        self.edge_weight(index).unwrap()
    }
}

impl<N, E, P> std::ops::IndexMut<EdgeIndex> for PortGraph<N, E, P> {
    fn index_mut(&mut self, index: EdgeIndex) -> &mut Self::Output {
        self.edge_weight_mut(index).unwrap()
    }
}

#[derive(Debug, Clone)]
struct Node<N> {
    weight: N,
    ports: EntityList<PortIndex>,
}

impl<N> Node<N> {
    pub fn remove_port(&mut self, port_index: PortIndex, pool: &mut ListPool<PortIndex>) {
        let index_in_node = self
            .ports
            .slice(pool)
            .iter()
            .position(|p| *p == port_index)
            .unwrap();

        let removed = self.ports.remove(index_in_node, pool);
        debug_assert_eq!(removed, port_index);
    }

    pub fn swap_remove_port(&mut self, port_index: PortIndex, pool: &mut ListPool<PortIndex>) {
        let index_in_node = self
            .ports
            .slice(pool)
            .iter()
            .position(|p| *p == port_index)
            .unwrap();

        let removed = self.ports.swap_remove(index_in_node, pool);
        debug_assert_eq!(removed, port_index);
    }
}

#[derive(Debug, Clone)]
struct Port<P> {
    weight: P,
    node: NodeIndex,
    edge: Option<EdgeIndex>,
}

#[derive(Debug, Clone)]
struct Edge<E> {
    weight: E,
    ports: EntityList<PortIndex>,
}

impl<E> Edge<E> {
    pub fn swap_remove_port(&mut self, port_index: PortIndex, pool: &mut ListPool<PortIndex>) {
        let index_in_edge = self
            .ports
            .slice(pool)
            .iter()
            .position(|p| *p == port_index)
            .unwrap();

        let removed = self.ports.swap_remove(index_in_edge, pool);
        debug_assert_eq!(removed, port_index);
    }
}
