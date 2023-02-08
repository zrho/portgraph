#[cfg(feature = "pyo3")]
use pyo3::prelude::*;
use std::fmt::{self, Debug};
use std::iter::{self, FusedIterator};

use crate::graph::{
    ConnectError, Direction, EdgeIndex, EdgeMap, MergeEdgesError, NodeIndex,
    NodeMap, PortIndex,
};
use crate::memory::{slab, Slab};

/// The graph's node type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<N> {
    /// Associated node data.
    weight: N,

    /// The first incoming and outgoing edge.
    edges: [Option<EdgeIndex>; 2],
}

impl<N> Node<N> {
    fn relink(&mut self, edge_map: &EdgeMap) {
        for i in 0..=1 {
            self.edges[i] = self.edges[i].and_then(|edge| edge_map.get(&edge)).copied();
        }
    }
}

/// The graph's edge type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge<E> {
    /// Associated edge data.
    weight: E,

    /// The nodes that the edge is connected to.
    ///
    /// The first component is the target and the second component the source of the edge. This
    /// is so that the array can be indexed by `Direction`.
    nodes: [Option<NodeIndex>; 2],

    /// Intrusive linked lists that point to the next edge connected to the edge's endpoints.
    next: [Option<EdgeIndex>; 2],
}

impl<E> Edge<E> {
    fn relink(&mut self, node_map: &NodeMap, edge_map: &EdgeMap) {
        for i in 0..=1 {
            self.next[i] = self.next[i].and_then(|edge| edge_map.get(&edge)).copied();
            self.nodes[i] = self.nodes[i].and_then(|node| node_map.get(&node)).copied();
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Graph<N, E> {
    nodes: Slab<NodeIndex, Node<N>>,
    edges: Slab<EdgeIndex, Edge<E>>,
}

impl<N: Debug, E: Debug> Debug for Graph<N, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Graph")
            .field("nodes", &self.nodes)
            .field("edges", &self.edges)
            .finish()
    }
}

impl<N, E> Default for Graph<N, E>
where
    N: Default,
    E: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

type NodeIndicesIterator<'a, N> = NodeIndices<'a, N>;
type NeighboursIterator<'a, N, E> = Neighbours<'a, N, E>;
type NodeEdgesIterator<'a, N, E> = NodeEdges<'a, N, E>;
type EdgeIndicesIterator<'a, E> = EdgeIndices<'a, E>;

impl<N, E> Graph<N, E>
where
    N: Default,
    E: Default,
{
    pub fn new() -> Self {
        Self::with_capacity(0, 0, 0)
    }

    pub fn with_capacity(nodes: usize, edges: usize, _ports: usize) -> Self {
        Self {
            nodes: Slab::with_capacity(nodes),
            edges: Slab::with_capacity(edges),
        }
    }

    pub fn add_node_unweighted(&mut self) -> NodeIndex {
        self.nodes.insert(Node {
            weight: Default::default(),
            edges: [None; 2],
        })
    }

    #[inline(always)]
    pub fn next_node_index(&self) -> NodeIndex {
        self.nodes.next_index()
    }

    pub fn add_node_with_edges_unweighted(
        &mut self,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> Result<NodeIndex, ConnectError> {
        let node = self.add_node_unweighted();
        self.connect_many(node, incoming, Direction::Incoming, None)?;
        self.connect_many(node, outgoing, Direction::Outgoing, None)?;
        Ok(node)
    }

    pub fn add_edge_unweighted(&mut self) -> EdgeIndex {
        self.edges.insert(Edge {
            weight: Default::default(),
            next: [None; 2],
            nodes: [None; 2],
        })
    }

    pub fn remove_node_unweighted(&mut self, node_index: NodeIndex) -> bool {
        let Some(node )= self.nodes.remove(node_index) else {return false;};

        for direction in Direction::ALL {
            let mut edge_index_next = node.edges[direction.index()];

            while let Some(edge_index) = edge_index_next {
                let edge = &mut self.edges[edge_index];
                edge.nodes[direction.index()] = None;
                edge_index_next = std::mem::take(&mut edge.next[direction.index()]);
            }
        }

        true
    }

    pub fn remove_edge_unweighted(&mut self, e: EdgeIndex) -> bool {
        self.disconnect(e, Direction::Incoming);
        self.disconnect(e, Direction::Outgoing);
        self.edges.remove(e).is_some()
    }

    pub fn has_node(&self, n: NodeIndex) -> bool {
        self.nodes.contains(n)
    }

    pub fn has_edge(&self, e: EdgeIndex) -> bool {
        self.edges.contains(e)
    }

    pub fn connect_after(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        edge_prev: EdgeIndex,
    ) -> Result<(), ConnectError> {
        if edge == edge_prev {
            return Err(ConnectError::SameEdge);
        }

        let (edge_data, edge_prev_data) = self
            .edges
            .get_mut_2(edge, edge_prev)
            .ok_or(ConnectError::UnknownEdge)?;

        if edge_prev_data.nodes[direction.index()] != Some(node) {
            return Err(ConnectError::NodeMismatch);
        } else if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        edge_data.nodes[direction.index()] = Some(node);
        edge_data.next[direction.index()] = edge_prev_data.next[direction.index()];
        edge_prev_data.next[direction.index()] = Some(edge);

        Ok(())
    }

    pub fn connect_first(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let node_data = self.nodes.get_mut(node).ok_or(ConnectError::UnknownNode)?;
        let edge_data = self.edges.get_mut(edge).ok_or(ConnectError::UnknownEdge)?;

        if edge_data.nodes[direction.index()].is_some() {
            return Err(ConnectError::AlreadyConnected);
        }

        edge_data.nodes[direction.index()] = Some(node);
        edge_data.next[direction.index()] = node_data.edges[direction.index()];
        node_data.edges[direction.index()] = Some(edge);

        Ok(())
    }

    pub fn connect(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        edge_prev: Option<EdgeIndex>,
    ) -> Result<(), ConnectError> {
        match edge_prev {
            Some(edge_prev) => self.connect_after(node, edge, direction, edge_prev),
            None => self.connect_first(node, edge, direction),
        }
    }

    pub fn connect_many(
        &mut self,
        node: NodeIndex,
        edges: impl IntoIterator<Item = EdgeIndex>,
        direction: Direction,
        mut edge_prev: Option<EdgeIndex>,
    ) -> Result<(), ConnectError> {
        for edge in edges {
            self.connect(node, edge, direction, edge_prev)?;
            edge_prev = Some(edge);
        }

        Ok(())
    }

    pub fn connect_last(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let edge_prev = self.node_edges(node, direction).last();
        self.connect(node, edge, direction, edge_prev)
    }

    pub fn disconnect(&mut self, edge_index: EdgeIndex, direction: Direction) {
        if !self.has_edge(edge_index) {
            return;
        }

        let prev = self.edge_prev(edge_index, direction);

        let edge = &mut self.edges[edge_index];
        let node = std::mem::take(&mut edge.nodes[direction.index()]);
        let next = std::mem::take(&mut edge.next[direction.index()]);

        let Some(node) = node else {
            return;
        };

        match prev {
            Some(prev) => self.edges[prev].next[direction.index()] = next,
            None => self.nodes[node].edges[direction.index()] = next,
        }
    }

    pub fn replace_connection(
        &mut self,
        prev: EdgeIndex,
        new: EdgeIndex,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        let n = self
            .edge_endpoint(prev, direction)
            .ok_or(ConnectError::UnknownEdge)?;

        self.connect_after(n, new, direction, prev)?;

        self.disconnect(prev, direction);
        Ok(())
    }

    pub fn insert_edge(
        &mut self,
        node: NodeIndex,
        edge: EdgeIndex,
        direction: Direction,
        index: usize,
    ) -> Result<(), ConnectError> {
        let edge_prev = if index == 0 {
            None
        } else {
            self.node_edges(node, direction).nth(index - 1)
        };

        self.connect(node, edge, direction, edge_prev)
    }

    pub fn edge_endpoint(&self, e: EdgeIndex, direction: Direction) -> Option<NodeIndex> {
        self.edges.get(e)?.nodes[direction.index()]
    }

    pub fn node_edges<'a>(&'a self, n: NodeIndex, direction: Direction) -> NodeEdgesIterator<'a, N, E> {
        let next = self
            .nodes
            .get(n)
            .and_then(|node| node.edges[direction.index()]);

        NodeEdges {
            graph: self,
            direction,
            next,
        }
    }

    pub fn neighbours<'a>(
        &'a self,
        n: NodeIndex,
        direction: Direction,
    ) -> NeighboursIterator<'a, N, E> {
        Neighbours {
            edges: self.node_edges(n, direction),
            graph: self,
            direction,
        }
    }

    pub fn node_indices<'a>(&'a self) -> NodeIndicesIterator<'a, N> {
        NodeIndices(self.nodes.iter())
    }

    pub fn edge_indices<'a>(&'a self) -> EdgeIndicesIterator<'a, E> {
        EdgeIndices(self.edges.iter())
    }

    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn port_count(&self) -> usize {
        todo!()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.edges.is_empty()
    }

    pub fn insert_graph(&mut self, other: Self) -> (NodeMap, EdgeMap) {
        let node_map: NodeMap = other
            .nodes
            .into_iter()
            .map(|(old_index, node)| {
                let new_index = self.add_node(node.weight);
                self.nodes[new_index].edges = node.edges;
                (old_index, new_index)
            })
            .collect();

        let edge_map: EdgeMap = other
            .edges
            .into_iter()
            .map(|(old_index, edge)| {
                let new_index = self.add_edge(edge.weight);
                self.edges[new_index].nodes = edge.nodes;
                self.edges[new_index].next = edge.next;
                (old_index, new_index)
            })
            .collect();

        for node_index in node_map.values() {
            self.nodes[*node_index].relink(&edge_map);
        }

        for edge_index in edge_map.values() {
            self.edges[*edge_index].relink(&node_map, &edge_map);
        }

        (node_map, edge_map)
    }

    pub fn compact(&mut self) -> (NodeMap, EdgeMap) {
        let mut node_map = NodeMap::new();
        let mut edge_map = EdgeMap::new();

        self.nodes.compact(|_, old_index, new_index| {
            node_map.insert(old_index, new_index);
        });

        self.edges.compact(|_, old_index, new_index| {
            edge_map.insert(old_index, new_index);
        });

        for (_, node) in self.nodes.iter_mut() {
            node.relink(&edge_map);
        }

        for (_, edge) in self.edges.iter_mut() {
            edge.relink(&node_map, &edge_map);
        }

        (node_map, edge_map)
    }

    pub fn shrink_to_fit(&mut self) {
        self.edges.shrink_to_fit();
        self.nodes.shrink_to_fit();
    }

    pub fn merge_edges_unweighted(
        &mut self,
        from: EdgeIndex,
        into: EdgeIndex,
    ) -> Result<(), MergeEdgesError> {
        self.merge_edges(from, into).map(|_| ())
    }

    /// Returns the index of the previous edge that is connected to the node in the given direction.
    pub fn edge_prev(&self, edge_index: EdgeIndex, direction: Direction) -> Option<EdgeIndex> {
        let node_index = self.edge_endpoint(edge_index, direction)?;

        self.node_edges(node_index, direction)
            .skip(1)
            .zip(self.node_edges(node_index, direction))
            .find(|(item, _)| *item == edge_index)
            .map(|(_, prev)| prev)
    }
}

type NodeWeightsIterator<'a, N> = NodeWeights<'a, N>;
type EdgeWeightsIterator<'a, E> = EdgeWeights<'a, E>;
type PortWeightsIterator<'a> = iter::Empty<(PortIndex, &'a ())>;

impl<N, E> Graph<N, E>
where
    N: Default,
    E: Default,
{

    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.nodes.insert(Node {
            weight,
            edges: [None; 2],
        })
    }

    pub fn add_node_with_edges(
        &mut self,
        weight: N,
        incoming: impl IntoIterator<Item = EdgeIndex>,
        outgoing: impl IntoIterator<Item = EdgeIndex>,
    ) -> Result<NodeIndex, ConnectError> {
        let node = self.add_node(weight);
        self.connect_many(node, incoming, Direction::Incoming, None)?;
        self.connect_many(node, outgoing, Direction::Outgoing, None)?;
        Ok(node)
    }

    pub fn add_edge(&mut self, weight: E) -> EdgeIndex {
        self.edges.insert(Edge {
            weight,
            next: [None; 2],
            nodes: [None; 2],
        })
    }

    pub fn remove_node(&mut self, node_index: NodeIndex) -> Option<N> {
        let node = self.nodes.remove(node_index)?;

        for direction in Direction::ALL {
            let mut edge_index_next = node.edges[direction.index()];

            while let Some(edge_index) = edge_index_next {
                let edge = &mut self.edges[edge_index];
                edge.nodes[direction.index()] = None;
                edge_index_next = std::mem::take(&mut edge.next[direction.index()]);
            }
        }

        Some(node.weight)
    }

    pub fn remove_edge(&mut self, e: EdgeIndex) -> Option<E> {
        self.disconnect(e, Direction::Incoming);
        self.disconnect(e, Direction::Outgoing);
        let edge = self.edges.remove(e)?;
        Some(edge.weight)
    }

    pub fn node_weight(&self, a: NodeIndex) -> Option<&N> {
        Some(&self.nodes.get(a)?.weight)
    }

    pub fn node_weight_mut(&mut self, a: NodeIndex) -> Option<&mut N> {
        Some(&mut self.nodes.get_mut(a)?.weight)
    }

    pub fn node_weights<'a>(&'a self) -> NodeWeightsIterator<'a, N> {
        NodeWeights(self.nodes.iter())
    }

    pub fn edge_weight(&self, e: EdgeIndex) -> Option<&E> {
        Some(&self.edges.get(e)?.weight)
    }

    pub fn edge_weight_mut(&mut self, e: EdgeIndex) -> Option<&mut E> {
        Some(&mut self.edges.get_mut(e)?.weight)
    }

    pub fn edge_weights<'a>(&'a self) -> EdgeWeightsIterator<'a, E> {
        EdgeWeights(self.edges.iter())
    }

    pub fn port_weight(&self, _e: PortIndex) -> Option<&()> {
        None
    }

    pub fn port_weight_mut(&mut self, _e: PortIndex) -> Option<&mut ()> {
        None
    }

    pub fn port_weights<'a>(&'a self) -> PortWeightsIterator<'a> {
        iter::empty()
    }

    pub fn merge_edges(&mut self, from: EdgeIndex, into: EdgeIndex) -> Result<E, MergeEdgesError> {
        if !self.has_edge(from) | !self.has_edge(into) {
            return Err(MergeEdgesError::UnknownEdge);
        }

        for direction in Direction::ALL {
            let from_node = self.edges[from].nodes[direction.index()];
            let into_node = self.edges[into].nodes[direction.index()];

            if from_node.is_some() && into_node.is_some() {
                return Err(MergeEdgesError::AlreadyConnected);
            }
        }

        for direction in Direction::ALL {
            let from_prev = self.edge_prev(from, direction);
            let from_edge = &mut self.edges[from];
            let from_next = std::mem::take(&mut from_edge.next[direction.index()]);
            let from_node = std::mem::take(&mut from_edge.nodes[direction.index()]);

            let Some(from_node) = from_node else {
                continue;
            };

            self.edges[into].nodes[direction.index()] = Some(from_node);
            self.edges[into].next[direction.index()] = from_next;

            match from_prev {
                Some(prev) => self.edges[prev].next[direction.index()] = Some(into),
                None => self.nodes[from_node].edges[direction.index()] = Some(into),
            }
        }

        Ok(self.remove_edge(from).unwrap())
    }
}

impl<N, E> std::ops::Index<NodeIndex> for Graph<N, E> {
    type Output = N;

    #[inline(always)]
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.nodes.get(index).unwrap().weight
    }
}

impl<N, E> std::ops::IndexMut<NodeIndex> for Graph<N, E> {
    #[inline(always)]
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.nodes.get_mut(index).unwrap().weight
    }
}

impl<N, E> std::ops::Index<EdgeIndex> for Graph<N, E> {
    type Output = E;

    #[inline(always)]
    fn index(&self, index: EdgeIndex) -> &Self::Output {
        &self.edges.get(index).unwrap().weight
    }
}

impl<N, E> std::ops::IndexMut<EdgeIndex> for Graph<N, E> {
    #[inline(always)]
    fn index_mut(&mut self, index: EdgeIndex) -> &mut Self::Output {
        &mut self.edges.get_mut(index).unwrap().weight
    }
}

/// Iterator created by [Graph::neighbours].
pub struct Neighbours<'a, N, E> {
    edges: NodeEdges<'a, N, E>,
    graph: &'a Graph<N, E>,
    direction: Direction,
}

impl<'a, N, E> Iterator for Neighbours<'a, N, E>
where
    N: Default,
    E: Default,
{
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let e = self.edges.next()?;
            if let Some(n) = self.graph.edge_endpoint(e, self.direction.reverse()) {
                return Some(n);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.edges.size_hint().1)
    }
}

impl<'a, N, E> ExactSizeIterator for Neighbours<'a, N, E>
where
    N: Default,
    E: Default,
{
}
impl<'a, N, E> FusedIterator for Neighbours<'a, N, E>
where
    N: Default,
    E: Default,
{
}

/// Iterator created by [Graph::node_edges].
#[derive(Clone)]
pub struct NodeEdges<'a, N, E> {
    graph: &'a Graph<N, E>,
    direction: Direction,
    next: Option<EdgeIndex>,
}

impl<'a, N, E> Iterator for NodeEdges<'a, N, E> {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.graph.edges[self.next?].next[self.direction.index()];
        std::mem::replace(&mut self.next, next)
    }
}

impl<'a, N, E> FusedIterator for NodeEdges<'a, N, E> {}

/// Iterator created by [Graph::node_indices].
pub struct NodeIndices<'a, N: 'a>(slab::Iter<'a, NodeIndex, Node<N>>);

impl<'a, N> Iterator for NodeIndices<'a, N> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for NodeIndices<'a, N> {}
impl<'a, N> FusedIterator for NodeIndices<'a, N> {}

/// Iterator created by [Graph::node_weights].
pub struct NodeWeights<'a, N: 'a>(slab::Iter<'a, NodeIndex, Node<N>>);

impl<'a, N> Iterator for NodeWeights<'a, N> {
    type Item = (NodeIndex, &'a N);

    fn next(&mut self) -> Option<Self::Item> {
        let (ix, n) = self.0.next()?;
        Some((ix, &n.weight))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for NodeWeights<'a, N> {}
impl<'a, N> FusedIterator for NodeWeights<'a, N> {}

/// Iterator created by [Graph::edge_weights].
pub struct EdgeWeights<'a, E: 'a>(slab::Iter<'a, EdgeIndex, Edge<E>>);

impl<'a, E> Iterator for EdgeWeights<'a, E> {
    type Item = (EdgeIndex, &'a E);

    fn next(&mut self) -> Option<Self::Item> {
        let (ix, n) = self.0.next()?;
        Some((ix, &n.weight))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for EdgeWeights<'a, N> {}
impl<'a, N> FusedIterator for EdgeWeights<'a, N> {}

/// Iterator created by [Graph::edge_indices].
pub struct EdgeIndices<'a, E: 'a>(slab::Iter<'a, EdgeIndex, Edge<E>>);

impl<'a, E> Iterator for EdgeIndices<'a, E> {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, N> ExactSizeIterator for EdgeIndices<'a, N> {}
impl<'a, N> FusedIterator for EdgeIndices<'a, N> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    pub fn merge_with_multiple_edges() {
        let mut graph = Graph::<i8, i8>::new();

        let e1 = graph.add_edge(-1);
        let e2 = graph.add_edge(-2);
        let e3 = graph.add_edge(-3);
        let e4 = graph.add_edge(-4);

        let n0 = graph.add_node_with_edges(0, [], [e1, e2, e3]).unwrap();
        let n1 = graph.add_node_with_edges(1, [e1, e4, e3], []).unwrap();

        assert_eq!(graph.merge_edges(e4, e2).unwrap(), -4);
        assert!(graph.node_edges(n0, Direction::Outgoing).eq([e1, e2, e3]));
        assert!(graph.node_edges(n1, Direction::Incoming).eq([e1, e2, e3]));
    }

    #[test]
    pub fn merge_edges_error() {
        let mut graph = Graph::<i8, i8>::new();

        let e1 = graph.add_edge(-1);
        let e2 = graph.add_edge(-2);
        let _ = graph.add_node_with_edges(0, [e1], []).unwrap();
        let _ = graph.add_node_with_edges(1, [e2], []).unwrap();

        assert!(graph.merge_edges(e2, e1).is_err());
    }
}
