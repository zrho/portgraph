// pub mod dot;
// #[allow(clippy::module_inception)]
// pub mod graph;
// pub mod substitute;
// pub mod toposort;

pub mod forest;
pub mod graph;
pub mod index;
pub mod memory;

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

/// Position in an ordered collection at which to insert a new element.
#[derive(Debug, Clone, Copy)]
pub enum Insert<T> {
    /// Insert as the first element.
    First,
    /// Insert as the last element.
    Last,
    /// Insert directly before a given element.
    Before(T),
    /// Insert directly after a given element.
    After(T),
    /// Insert after a given number of elements.
    Index(usize),
}

// #[cfg(feature = "pyo3")]
// pub mod py_graph;

// #[cfg(test)]
// mod tests {
//     use std::collections::{BTreeMap, HashSet};

//     use crate::{
//         dot::dot_string,
//         graph::{EdgeIndex, NodeIndex},
//     };

//     use super::graph::Graph;

//     #[test]
//     fn test_insert_graph() {
//         let mut g = Graph::<i8, i8>::with_capacity(3, 2);

//         let e1 = g.add_edge(-1);
//         let e2 = g.add_edge(-2);

//         let _n0 = g.add_node_with_edges(0, [], [e1]).unwrap();
//         let _n1 = g.add_node_with_edges(1, [e1], [e2]).unwrap();
//         let _n2 = g.add_node_with_edges(2, [e2], []).unwrap();

//         let mut g2 = Graph::<i8, i8>::with_capacity(2, 1);

//         let e3 = g2.add_edge(-3); //(g20, 0), (g21, 0), -3);
//         let _n3 = g2.add_node_with_edges(3, [], [e3]);
//         let _n4 = g2.add_node_with_edges(4, [e3], []);

//         g.insert_graph(g2);

//         let correct_weights: HashSet<_> = HashSet::from_iter([0, 1, 2, 3, 4].into_iter());
//         assert_eq!(
//             HashSet::from_iter(g.node_weights().copied()),
//             correct_weights
//         );

//         let correct_weights: HashSet<_> = HashSet::from_iter([-1, -2, -3].into_iter());
//         assert_eq!(
//             HashSet::from_iter(g.edge_weights().copied()),
//             correct_weights
//         );
//     }

//     #[test]
//     fn test_remove_invalid() {
//         let mut g = Graph::<i8, i8>::with_capacity(3, 2);

//         let e1 = g.add_edge(-1);
//         let e2 = g.add_edge(-2);
//         let e3 = g.add_edge(-3);

//         let _n0 = g.add_node_with_edges(0, [], [e1, e3]).unwrap();
//         let n1 = g.add_node_with_edges(1, [e1], [e2]).unwrap();
//         let _n2 = g.add_node_with_edges(2, [e2, e3], []).unwrap();

//         assert_eq!(g.node_count(), 3);
//         assert_eq!(g.edge_count(), 3);

//         assert_eq!(g.remove_node(n1), Some(1));
//         assert_eq!(g.remove_edge(e1), Some(-1));
//         assert_eq!(g.remove_edge(e2), Some(-2));

//         assert_eq!(g.node_count(), 2);
//         assert_eq!(g.edge_count(), 1);

//         let (nodemap, edgemap) = g.compact();

//         assert_eq!(g.node_count(), 2);
//         assert_eq!(g.edge_count(), 1);

//         assert_eq!(
//             nodemap,
//             BTreeMap::from_iter([
//                 (NodeIndex::new(0), NodeIndex::new(0)),
//                 (NodeIndex::new(2), NodeIndex::new(1))
//             ])
//         );

//         assert_eq!(
//             edgemap,
//             BTreeMap::from_iter([(EdgeIndex::new(2), EdgeIndex::new(0)),])
//         );

//         // TODO some better test of validity (check graph correctness conditions)
//         let _s = dot_string(&g);
//     }
// }
