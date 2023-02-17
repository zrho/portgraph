use std::marker::PhantomData;

use crate::{Graph, NodeIndex, PortIndex};

/// A graph view that exposes a single hierarchical layer of a graph, where all the nodes are the children of a given parent.
///
/// TODO: It would probably be more efficient to show all same-level nodes,
/// independently of the parent (since we would then be able to follow links without checking).
struct LayerView<G, N, NV, P, PV, FN, FP> {
    graph: G,
    parent: NodeIndex,
    node_map: FN,
    port_map: FP,
    phantom: PhantomData<(N, NV, P, PV)>,
}

impl<G, N, NV, P, PV, FN, FP> LayerView<G, N, NV, P, PV, FN, FP>
where
    for<'a> G: Graph<'a, N, P>,
    N: Clone,
    P: Clone,
    NV: Clone,
    PV: Clone,
    FN: Fn(NodeIndex, N) -> NV,
    FN: Fn(PortIndex, P) -> PV,
{
    pub fn new(graph: G, parent: NodeIndex, node_map: FN, port_map: FP) -> Self {
        Self {
            graph,
            parent,
            node_map,
            port_map,
            phantom: PhantomData,
        }
    }
}

// TODO: Use the impl delegation macro from petgraph. We will need to modify it to be able to manually define some methods.
impl<'a, G, N, NV, P, PV, FN, FP> Graph<'a, NV, PV> for LayerView<G, N, NV, P, PV, FN, FP>
where
    G: Graph<'a, N, P>,
    N: 'a + Clone,
    P: 'a + Clone,
    NV: 'a + Clone,
    PV: 'a + Clone,
    FN: Fn(NodeIndex, &N) -> &NV,
    FP: Fn(PortIndex, &P) -> &PV,
{
    fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    fn port_count(&self) -> usize {
        self.graph.port_count()
    }

    fn edge_count(&self) -> usize {
        todo!()
    }

    fn contains_node(&self, node: NodeIndex) -> bool {
        if !self.graph.contains_node(node) {
            return false;
        }
        self.graph.node_parent(node) == Some(self.parent)
    }

    fn contains_port(&self, port: PortIndex) -> bool {
        self.graph.contains_port(port)
    }

    fn is_empty(&self) -> bool {
        self.graph.is_empty()
            || self
                .graph
                .nodes_iter()
                .all(|v| self.graph.node_parent(v) != Some(self.parent))
    }

    fn node_port_count(&self, _node: NodeIndex, _direction: crate::Direction) -> usize {
        todo!()
    }

    // Filter out nodes that are not children of the parent.
    fn nodes_iter(&self) -> crate::unweighted::Nodes {
        todo!()
    }

    fn ports_iter(&self) -> crate::unweighted::Ports {
        self.graph.ports_iter()
    }

    fn port_index(
        &self,
        node: NodeIndex,
        offset: usize,
        direction: crate::Direction,
    ) -> Option<PortIndex> {
        self.graph.port_index(node, offset, direction)
    }

    fn port_offset(&self, port: PortIndex) -> Option<usize> {
        self.graph.port_offset(port)
    }

    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.graph.input(node, offset)
    }

    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.graph.output(node, offset)
    }

    fn ports(&self, node: NodeIndex, direction: crate::Direction) -> crate::unweighted::NodePorts {
        self.graph.ports(node, direction)
    }

    fn inputs(&self, node: NodeIndex) -> crate::unweighted::NodePorts {
        self.graph.inputs(node)
    }

    fn outputs(&self, node: NodeIndex) -> crate::unweighted::NodePorts {
        self.graph.outputs(node)
    }

    fn links(&self, node: NodeIndex, direction: crate::Direction) -> &[Option<PortIndex>] {
        self.graph.links(node, direction)
    }

    fn input_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.graph.input_links(node)
    }

    fn output_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.graph.output_links(node)
    }

    fn neighbours(
        &self,
        _node: NodeIndex,
        _direction: crate::Direction,
    ) -> std::iter::Empty<NodeIndex> {
        todo!()
    }

    fn connected(&self, from: NodeIndex, to: NodeIndex) -> Option<(PortIndex, PortIndex)> {
        self.graph.connected(from, to)
    }

    fn port_node(&self, port: PortIndex) -> Option<NodeIndex> {
        self.graph.port_node(port)
    }

    fn node_weight(&'a self, node: NodeIndex) -> Option<&'a NV> {
        self.graph.node_weight(node).map(|w| {
            let f = &self.node_map;
            f(node, w)
        })
    }

    fn node_weights(&'a self) -> std::iter::Empty<(NodeIndex, &'a NV)> {
        todo!()
    }

    fn port_weight(&'a self, port: PortIndex) -> Option<&'a PV> {
        self.graph.port_weight(port).map(|w| {
            let f = &self.port_map;
            f(port, w)
        })
    }

    fn port_weights(&'a self) -> std::iter::Empty<(PortIndex, &'a NV)> {
        todo!()
    }

    fn port_link(&self, port: PortIndex) -> Option<PortIndex> {
        self.graph.port_link(port)
    }

    fn is_linked(&self, port: PortIndex) -> bool {
        self.graph.is_linked(port)
    }

    fn node_child_count(&self, node: NodeIndex) -> usize {
        self.graph.node_child_count(node)
    }

    fn node_parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.graph.node_parent(node)
    }

    fn node_first_child(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.graph.node_first_child(node)
    }

    fn node_last_child(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.graph.node_last_child(node)
    }

    fn node_children(&self, node: NodeIndex) -> crate::hierarchy::Children<'_> {
        self.graph.node_children(node)
    }

    fn node_next_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.graph.node_next_sibling(node)
    }

    fn node_prev_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.graph.node_prev_sibling(node)
    }
}
