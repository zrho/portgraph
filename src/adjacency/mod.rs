
pub mod inline;
pub mod linked;

pub use inline::InlineGraph;
pub use linked::LinkedGraph;

use crate::{NodeIndex, EdgeIndex, ConnectError, Direction, Insert};
use crate::memory::EntityIndex;

/// Trait for graphs that encode edges connecting nodes.
pub trait Adjacency<NI = NodeIndex, EI = EdgeIndex>
where
    NI: EntityIndex,
    EI: EntityIndex,
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
    fn edge_endpoint(&self, e: EI, direction: Direction) -> Option<(NI, usize)>;

    /// Shorthand for [`Graph::edge_endpoint`] in the outgoing direction.
    #[inline]
    fn source(&self, edge: EI) -> Option<(NI, usize)> {
        self.edge_endpoint(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_endpoint`] in the incoming direction.
    #[inline]
    fn target(&self, edge: EI) -> Option<(NI, usize)> {
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
    fn edge_position(&self, edge: EI, dir: Direction) -> Option<usize> {
        self.edge_endpoint(edge, dir).map(|(_, position)| position)
    }

    /// Shorthand for [`Graph::edge_position`] in the outgoing direction.
    #[inline]
    fn source_position(&self, edge: EI) -> Option<usize> {
        self.edge_position(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_position`] in the incoming direction.
    #[inline]
    fn target_position(&self, edge: EI) -> Option<usize> {
        self.edge_position(edge, Direction::Incoming)
    }
}

/// Trait for graphs that encode edges connecting nodes.
pub trait AdjacencyMut<NI = NodeIndex, EI = EdgeIndex> : Adjacency<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{

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
        I: IntoIterator<Item = EI> {
        for edge in edges {
            // Note: This may connect edges in an inverse order for some Insert variants.
            self.connect(node, edge, position, direction)?;
        }
        Ok(())
    }

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
    fn disconnect(&mut self, edge_index: EI, direction: Direction) -> Option<NI>;
    
    /// Disconnects all edges connected to a `node`.
    fn clear_node(&mut self, node: NI);

    /// Disconnects an edge in both directions.
    fn clear_edge(&mut self, edge: EI);
}

/// [`Graph`] which supports accessing a slice of incident edges.
pub trait AdjacencySlice<NI, EI>: Adjacency<NI, EI>
where NI: EntityIndex,
      EI: EntityIndex,
{
    /// Returns a slice containing the edges connected to a node in a specified direction.
    fn node_edges_slice(&self, node: NI, dir: Direction) -> &[EI];
}
