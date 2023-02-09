//! Components defining a graph structure.
//!
//! Every node has an ordered list of incoming and outgoing edges. An edge is
//! connected to at most one node in each direction. In particular, there may be
//! dangling edges which are not connected to a node on one or both sides.

pub mod componentgraph;
pub mod inline;
pub mod linked;

pub use componentgraph::PortGraph;
pub use inline::InlineGraph;
pub use linked::LinkedGraph;
