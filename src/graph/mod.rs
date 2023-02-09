//! Components defining a graph structure.
//!
//! Every node has an ordered list of incoming and outgoing edges. An edge is
//! connected to at most one node in each direction. In particular, there may be
//! dangling edges which are not connected to a node on one or both sides.

use thiserror::Error;
pub mod componentgraph;
pub mod components;
pub mod inline;
pub mod linked;

pub use inline::InlineGraph;
pub use linked::LinkedGraph;

use crate::{Direction, Insert};

/// A directed graph with ordered adjacency lists.
pub trait Graph {
    type Node;
    type Edge;

    /// Iterator over the edges connected to a node.
    type NodeEdges<'a>: Iterator<Item = Self::Edge>
    where
        Self: 'a;

    /// Iterator over the edges that are connected to a node.
    fn node_edges(&self, node: Self::Node, dir: Direction) -> Self::NodeEdges<'_>;

    /// Shorthand for [`Graph::node_edges`] in the incoming direction.
    #[inline]
    fn inputs(&self, node: Self::Node) -> Self::NodeEdges<'_> {
        self.node_edges(node, Direction::Incoming)
    }

    /// Shorthand for [`Graph::node_edges`] in the outgoing direction.
    #[inline]
    fn outputs(&self, node: Self::Node) -> Self::NodeEdges<'_> {
        self.node_edges(node, Direction::Outgoing)
    }

    /// Returns the node and position that the `edge` is connected to.
    ///
    /// `None` if the edge does not exist or is not connected in the direction.
    fn edge_endpoint(&self, edge: Self::Edge, dir: Direction) -> Option<(Self::Node, usize)>;

    /// Shorthand for [`Graph::edge_endpoint`] in the outgoing direction.
    #[inline]
    fn source(&self, edge: Self::Edge) -> Option<(Self::Node, usize)> {
        self.edge_endpoint(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_endpoint`] in the incoming direction.
    #[inline]
    fn target(&self, edge: Self::Edge) -> Option<(Self::Node, usize)> {
        self.edge_endpoint(edge, Direction::Incoming)
    }

    /// Returns the node that the `edge` is connected to.
    ///
    /// `None` if the edge does not exist or is not connected in the direction.
    #[inline]
    fn edge_node(&self, edge: Self::Edge, dir: Direction) -> Option<Self::Node> {
        self.edge_endpoint(edge, dir).map(|(node, _)| node)
    }

    /// Shorthand for [`Graph::edge_node`] in the outgoing direction.
    #[inline]
    fn source_node(&self, edge: Self::Edge) -> Option<Self::Node> {
        self.edge_node(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_node`] in the incoming direction.
    #[inline]
    fn target_node(&self, edge: Self::Edge) -> Option<Self::Node> {
        self.edge_node(edge, Direction::Incoming)
    }

    /// Returns the position in the node's edge list an `edge` is connected to.
    ///
    /// `None` if the edge does not exist or is not connected in the direction.
    #[inline]
    fn edge_position(&self, edge: Self::Edge, dir: Direction) -> Option<usize> {
        self.edge_endpoint(edge, dir).map(|(_, position)| position)
    }

    /// Shorthand for [`Graph::edge_position`] in the outgoing direction.
    #[inline]
    fn source_position(&self, edge: Self::Edge) -> Option<usize> {
        self.edge_position(edge, Direction::Outgoing)
    }

    /// Shorthand for [`Graph::edge_position`] in the incoming direction.
    #[inline]
    fn target_position(&self, edge: Self::Edge) -> Option<usize> {
        self.edge_position(edge, Direction::Incoming)
    }
}

/// [`Graph`] which admits connecting and disconnecting edges.
pub trait GraphMut: Graph {
    /// Connect an edge to an incoming or outgoing port of a node.
    ///
    /// # Errors
    ///
    ///  - When the edge is already connected.
    ///  - When trying to insert relative to an edge that is not connected to the same node.
    ///
    /// In the case of an error, the graph is unchanged.
    fn connect(
        &mut self,
        node: Self::Node,
        edge: Self::Edge,
        position: Insert<Self::Edge>,
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
        node: Self::Node,
        edges: I,
        position: Insert<Self::Edge>,
        direction: Direction,
    ) -> Result<(), ConnectError>
    where
        I: IntoIterator<Item = Self::Edge>;

    /// Disconnects an edge in a given direction, returning the node it was connected to.
    ///
    /// Returns `None` when the edge is not connected.
    fn disconnect(&mut self, edge: Self::Edge, direction: Direction) -> Option<Self::Node>;

    /// Disconnects all edges connected to a `node`.
    fn clear_node(&mut self, node: Self::Node);

    /// Disconnects an edge in both directions.
    fn clear_edge(&mut self, edge: Self::Edge);
}

/// [`Graph`] which supports accessing a slice of incident edges.
pub trait GraphSlice: Graph {
    /// Returns a slice containing the edges connected to a node in a specified direction.
    fn node_edges_slice(&self, node: Self::Node, dir: Direction) -> &[Self::Edge];
}

/// [`Graph`] which does not manage its own indices.
///
/// Indices of nodes and edges are not maintained by the structure; instead
/// every index value points to a node or edge which is not connected. These
/// components are intended to be used by some other structure like [`Slab`]
/// which keeps track of which indices are valid.
///
/// [`Slab`]: crate::memory::Slab
pub trait GraphSecondary: Graph + Default {
    /// Changes the key of a node.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    fn rekey_node(&mut self, old: Self::Node, new: Self::Node);

    /// Changes the key of an edge.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    fn rekey_edge(&mut self, old: Self::Edge, new: Self::Edge);

    // TODO: Capacity functions
}

#[derive(Debug, Clone, Error)]
pub enum ConnectError {
    #[error("the edge was already connected to another node")]
    EdgeAlreadyConnected,
    #[error("can not insert an edge relative to a disconnected one")]
    RelativeToDisconnected,
    #[error("edges must be connected to the same node")]
    NodeMismatch,
}
