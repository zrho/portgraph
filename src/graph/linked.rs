//! Secondary graph data structure with doubly linked adjacency lists.
#[cfg(feature = "pyo3")]
use pyo3::prelude::*;
use std::fmt::Debug;
use std::iter::FusedIterator;
use std::mem::{replace, take};

use crate::memory::map::SecondaryMap;
use crate::memory::EntityIndex;
use crate::{Direction, Insert};

use super::{ConnectError, Graph, GraphMut, GraphSecondary};

/// Secondary graph data structure with doubly linked adjacency lists.
#[derive(Clone)]
pub struct LinkedGraph<NI, EI> {
    nodes: SecondaryMap<NI, NodeData<EI>>,
    edges: SecondaryMap<EI, EdgeData<NI, EI>>,
}

impl<NI, EI> Default for LinkedGraph<NI, EI> {
    fn default() -> Self {
        Self::new()
    }
}

impl<NI, EI> LinkedGraph<NI, EI> {
    pub fn new() -> Self {
        Self {
            nodes: SecondaryMap::new(),
            edges: SecondaryMap::new(),
        }
    }
}

impl<NI, EI> LinkedGraph<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn connect_last(&mut self, node: NI, edge: EI, dir: Direction) -> Result<(), ConnectError> {
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[dir.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        let node_data = &mut self.nodes[node];
        node_data.len[dir.index()] += 1;
        let edge_prev = replace(&mut node_data.last[dir.index()], Some(edge));

        edge_data.nodes[dir.index()] = Some(node);
        edge_data.prev[dir.index()] = edge_prev;

        match edge_prev {
            Some(edge_prev) => self.edges[edge_prev].next[dir.index()] = Some(edge),
            None => node_data.first[dir.index()] = Some(edge),
        }

        Ok(())
    }

    fn connect_first(&mut self, node: NI, edge: EI, dir: Direction) -> Result<(), ConnectError> {
        let edge_data = &mut self.edges[edge];

        if edge_data.nodes[dir.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        let node_data = &mut self.nodes[node];
        node_data.len[dir.index()] += 1;
        let edge_next = replace(&mut node_data.first[dir.index()], Some(edge));

        edge_data.nodes[dir.index()] = Some(node);
        edge_data.next[dir.index()] = edge_next;

        match edge_next {
            Some(edge_next) => self.edges[edge_next].prev[dir.index()] = Some(edge),
            None => node_data.last[dir.index()] = Some(edge),
        }

        Ok(())
    }

    fn connect_before(&mut self, edge: EI, before: EI, dir: Direction) -> Result<(), ConnectError> {
        if self.edges[edge].nodes[dir.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        let before_data = &mut self.edges[before];

        let Some(node) = before_data.nodes[dir.index()] else {
            return Err(ConnectError::RelativeToDisconnected);
        };

        let node_data = &mut self.nodes[node];
        node_data.len[dir.index()] += 1;

        let before_prev = replace(&mut before_data.prev[dir.index()], Some(edge));

        {
            let edge_data = &mut self.edges[edge];
            edge_data.nodes[dir.index()] = Some(node);
            edge_data.next[dir.index()] = Some(before);
            edge_data.prev[dir.index()] = before_prev;
        }

        match before_prev {
            Some(prev) => self.edges[prev].next[dir.index()] = Some(edge),
            None => node_data.first[dir.index()] = Some(edge),
        }

        Ok(())
    }

    fn connect_after(&mut self, edge: EI, after: EI, dir: Direction) -> Result<(), ConnectError> {
        if self.edges[edge].nodes[dir.index()].is_some() {
            return Err(ConnectError::EdgeAlreadyConnected);
        }

        let after_data = &mut self.edges[after];

        let Some(node) = after_data.nodes[dir.index()] else {
            return Err(ConnectError::RelativeToDisconnected);
        };

        let node_data = &mut self.nodes[node];
        node_data.len[dir.index()] += 1;

        let after_next = replace(&mut after_data.next[dir.index()], Some(edge));

        {
            let edge_data = &mut self.edges[edge];
            edge_data.nodes[dir.index()] = Some(node);
            edge_data.prev[dir.index()] = Some(after);
            edge_data.next[dir.index()] = after_next;
        }

        match after_next {
            Some(next) => self.edges[next].prev[dir.index()] = Some(edge),
            None => node_data.last[dir.index()] = Some(edge),
        }

        Ok(())
    }

    fn connect_at(
        &mut self,
        node: NI,
        edge: EI,
        index: usize,
        dir: Direction,
    ) -> Result<(), ConnectError> {
        match self.node_edges(node, dir).nth(index) {
            Some(before) => self.connect_before(edge, before, dir),
            None => self.connect_last(node, edge, dir),
        }
    }

    #[inline]
    pub fn edge_next(&self, edge: EI, dir: Direction) -> Option<EI> {
        self.edges[edge].next[dir.index()]
    }

    #[inline]
    pub fn edge_prev(&self, edge: EI, dir: Direction) -> Option<EI> {
        self.edges[edge].prev[dir.index()]
    }

    #[inline]
    pub fn edge_first(&self, node: NI, dir: Direction) -> Option<EI> {
        self.nodes[node].first[dir.index()]
    }

    #[inline]
    pub fn edge_last(&self, node: NI, dir: Direction) -> Option<EI> {
        self.nodes[node].last[dir.index()]
    }
}

impl<NI, EI> Graph for LinkedGraph<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    type Node = NI;
    type Edge = EI;

    type NodeEdges<'a> = NodeEdges<'a, NI, EI>
    where
        Self: 'a;

    fn node_edges(&self, node: Self::Node, dir: Direction) -> Self::NodeEdges<'_> {
        let node_data = &self.nodes[node];
        NodeEdges {
            graph: self,
            next: node_data.first[dir.index()],
            prev: node_data.last[dir.index()],
            len: node_data.len[dir.index()] as usize,
            direction: dir,
        }
    }

    fn edge_node(&self, edge: Self::Edge, dir: Direction) -> Option<Self::Node> {
        self.edges.get(edge)?.nodes[dir.index()]
    }

    fn edge_endpoint(&self, edge: Self::Edge, dir: Direction) -> Option<(Self::Node, usize)> {
        let edge_data = self.edges.get(edge)?;
        let node = edge_data.nodes[dir.index()]?;
        let port = self.node_edges(node, dir).position(|e| e == edge)?;
        Some((node, port))
    }
}

impl<NI, EI> GraphMut for LinkedGraph<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn connect(
        &mut self,
        node: Self::Node,
        edge: Self::Edge,
        position: Insert<Self::Edge>,
        direction: Direction,
    ) -> Result<(), ConnectError> {
        // TODO: For the relative connection, check that the node matches
        match position {
            Insert::First => self.connect_first(node, edge, direction),
            Insert::Last => self.connect_last(node, edge, direction),
            Insert::Before(before) => self.connect_before(edge, before, direction),
            Insert::After(after) => self.connect_after(edge, after, direction),
            Insert::Index(index) => self.connect_at(node, edge, index, direction),
        }
    }

    fn connect_many<I>(
        &mut self,
        node: Self::Node,
        edges: I,
        position: Insert<Self::Edge>,
        direction: Direction,
    ) -> Result<(), ConnectError>
    where
        I: IntoIterator<Item = Self::Edge>,
    {
        todo!()
    }

    fn disconnect(&mut self, edge: Self::Edge, direction: Direction) -> Option<Self::Node> {
        let Some(edge_data) = self.edges.get_mut(edge) else {
            return None;
        };

        let node = take(&mut edge_data.nodes[direction.index()]);
        let prev = take(&mut edge_data.prev[direction.index()]);
        let next = take(&mut edge_data.next[direction.index()]);

        if let Some(node) = node {
            let node_data = &mut self.nodes[node];
            node_data.len[direction.index()] -= 1;

            match prev {
                Some(prev) => self.edges[prev].next[direction.index()] = next,
                None => node_data.first[direction.index()] = next,
            }

            match next {
                Some(next) => self.edges[next].prev[direction.index()] = prev,
                None => node_data.last[direction.index()] = prev,
            }
        }

        node
    }

    fn clear_node(&mut self, node: Self::Node) {
        let Some(node_data) = self.nodes.take(node) else {
            return;
        };

        for direction in Direction::ALL {
            let mut edge_next = node_data.first[direction.index()];

            while let Some(edge) = edge_next {
                let mut edge_data = &mut self.edges[edge];
                edge_data.nodes[direction.index()] = None;
                edge_data.prev[direction.index()] = None;
                edge_next = take(&mut edge_data.next[direction.index()]);
            }
        }
    }

    fn clear_edge(&mut self, edge: Self::Edge) {
        for direction in Direction::ALL {
            self.disconnect(edge, direction);
        }
    }
}

impl<NI, EI> GraphSecondary for LinkedGraph<NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn rekey_node(&mut self, old: Self::Node, new: Self::Node) {
        todo!()
    }

    fn rekey_edge(&mut self, old: Self::Edge, new: Self::Edge) {
        todo!()
    }
}

#[derive(Clone)]
pub struct NodeEdges<'a, NI, EI> {
    graph: &'a LinkedGraph<NI, EI>,
    next: Option<EI>,
    prev: Option<EI>,
    len: usize,
    direction: Direction,
}

impl<'a, NI, EI> Iterator for NodeEdges<'a, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    type Item = EI;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.next.unwrap();
        self.next = self.graph.edge_next(current, self.direction);
        Some(current)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }
}

impl<'a, NI, EI> DoubleEndedIterator for NodeEdges<'a, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.prev.unwrap();
        self.prev = self.graph.edge_prev(current, self.direction);
        Some(current)
    }
}

impl<'a, NI, EI> ExactSizeIterator for NodeEdges<'a, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, NI, EI> FusedIterator for NodeEdges<'a, NI, EI>
where
    NI: EntityIndex,
    EI: EntityIndex,
{
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NodeData<EI> {
    /// The first incoming and outgoing edge.
    first: [Option<EI>; 2],
    /// The last incoming and outgoing edge.
    last: [Option<EI>; 2],
    /// The number of incoming and outgoing edges.
    len: [u16; 2],
}

impl<EI> Default for NodeData<EI> {
    fn default() -> Self {
        Self {
            first: Default::default(),
            last: Default::default(),
            len: [0; 2],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EdgeData<NI, EI> {
    /// The nodes that the edge is connected to.
    ///
    /// The first component is the target and the second component the source of the edge. This
    /// is so that the array can be indexed by `Direction`.
    nodes: [Option<NI>; 2],
    /// Intrusive linked lists that point to the next edge connected to the edge's endpoints.
    prev: [Option<EI>; 2],
    /// Intrusive linked lists that point to the previous edge connected to the edge's endpoints.
    next: [Option<EI>; 2],
}

impl<NI, EI> Default for EdgeData<NI, EI> {
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            next: Default::default(),
            prev: Default::default(),
        }
    }
}
