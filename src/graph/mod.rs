//! Components defining a graph structure on node and edge indices.
//!
//! The graph component structure consists of nodes and edges identified by
//! their index.  Indices are not maintained by the structure; instead every
//! index value points to a node or edge which is not connected. These
//! components are intended to be used by some other structure like [`Slab`] which
//! keeps track of which indices are valid.
//!
//! Every node has an ordered list of incoming and outgoing edges.  An edge is
//! connected to at most one node in each direction. In particular, there are
//! dangling edges which are not connected to a node on one or both sides.
//!
//! [`Slab`]: crate::memory::Slab

use thiserror::Error;

// TODO define a trait with the common operations for the graph component
// TODO convert the linked list graph into a graph component like `InlineGraph`

/// Error returned by [Graph::merge_edges].
#[derive(Debug, Error)]
pub enum MergeEdgesError {
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
}

#[derive(Debug, Clone, Error)]
pub enum ConnectError {
    #[error("the edge was already connected to another node")]
    EdgeAlreadyConnected,
    #[error("can not insert an edge relative to a disconnected one")]
    RelativeToDisconnected,
}
