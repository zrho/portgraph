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

mod inline;
mod traits;
mod linked;

pub use inline::InlineGraph;
use thiserror::Error;
pub use traits::{
    BasePortGraph, EdgeMap, IntoLayout, NodeMap, WeightedPortGraph,
};
pub use linked::Graph;

use crate::memory::make_entity;

// TODO define a trait with the common operations for the graph component
// TODO convert the linked list graph into a graph component like `InlineGraph`

#[cfg_attr(feature = "pyo3", pyclass)]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Direction {
    Incoming = 0,
    Outgoing = 1,
}

impl Default for Direction {
    #[inline(always)]
    fn default() -> Self {
        Direction::Incoming
    }
}

impl Direction {
    pub const ALL: [Direction; 2] = [Direction::Incoming, Direction::Outgoing];

    #[inline(always)]
    pub fn index(self) -> usize {
        self as usize
    }

    #[inline(always)]
    pub fn reverse(self) -> Direction {
        match self {
            Direction::Incoming => Direction::Outgoing,
            Direction::Outgoing => Direction::Incoming,
        }
    }
}

make_entity! {
    pub struct NodeIndex(u32);
    pub struct RegionIndex(u32);
    pub struct EdgeIndex(u32);
    pub struct PortIndex(u32);
}

/// Error returned by [Graph::connect] and similar methods.
#[derive(Debug, Error)]
pub enum ConnectError {
    #[error("unknown node")]
    UnknownNode,
    #[error("unknown edge")]
    UnknownEdge,
    #[error("node mismatch")]
    NodeMismatch,
    #[error("edge is already connected")]
    AlreadyConnected,
    #[error("can not connect edge relative to itself")]
    SameEdge,
    #[error("port index is out of bounds")]
    OutOfBounds,
}

/// Error returned by [Graph::merge_edges].
#[derive(Debug, Error)]
pub enum MergeEdgesError {
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
}
