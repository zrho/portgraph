//! Components defining a forest structure on node indices.
//!
/// Every node has an ordered collection of child nodes. The root nodes, i.e.
/// the nodes that do not have any parent, are not ordered themselves.  When a
/// node has not been set as the child or parent of any other node it is
/// implicitly considered to be a root node.
mod linked;

pub use linked::LinkedForest;
