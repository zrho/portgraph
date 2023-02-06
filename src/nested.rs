use std::mem::{replace, take};

use crate::{graph::Graph, EdgeIndex, NodeIndex};

pub struct NestedGraph<N, E> {
    inner: Graph<InnerNode<N>, E>,
}

impl<N, E> NestedGraph<N, E> {
    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.inner.add_node(InnerNode {
            weight,
            children: [None; 2],
            parent: None,
            siblings: [None; 2],
        })
    }

    pub fn remove_node(&mut self, node: NodeIndex) -> Option<N> {
        self.detach_node(node);
        let node = self.inner.remove_node(node)?;

        // Detach all the children of the node.
        let mut child_next = node.children[0];

        while let Some(child) = child_next {
            let child_data = &mut self.inner[child];
            child_data.parent = None;
            let siblings = take(&mut child_data.siblings);
            child_next = siblings[1];
        }

        Some(node.weight)
    }

    #[inline]
    pub fn node_weight(&self, node: NodeIndex) -> Option<&N> {
        Some(&self.inner.node_weight(node)?.weight)
    }

    #[inline]
    pub fn node_weight_mut(&mut self, node: NodeIndex) -> Option<&mut N> {
        Some(&mut self.inner.node_weight_mut(node)?.weight)
    }

    #[inline]
    pub fn has_node(&self, node: NodeIndex) -> bool {
        self.inner.has_node(node)
    }
}

impl<N, E> NestedGraph<N, E> {
    pub fn add_edge(&mut self, weight: E) -> EdgeIndex {
        self.inner.add_edge(weight)
    }
}

impl<N, E> NestedGraph<N, E> {
    pub fn attach_node_last(&mut self, node: NodeIndex, parent: NodeIndex) {
        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        } else if self.inner[node].parent.is_some() {
            panic!("node was already attached");
        }

        self.inner[node].parent = Some(parent);

        match replace(&mut self.inner[parent].children[1], Some(node)) {
            Some(prev) => self.inner[prev].siblings[1] = Some(node),
            None => self.inner[parent].children[0] = Some(node),
        }
    }

    pub fn attach_node_first(&mut self, node: NodeIndex, parent: NodeIndex) {
        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        } else if self.inner[node].parent.is_some() {
            panic!("node was already attached");
        }

        self.inner[node].parent = Some(parent);

        match replace(&mut self.inner[parent].children[0], Some(node)) {
            Some(next) => self.inner[next].siblings[0] = Some(node),
            None => self.inner[parent].children[1] = Some(node),
        }
    }

    pub fn attach_node_before(&mut self, node: NodeIndex, before: NodeIndex) {
        if self.inner[node].parent.is_some() {
            panic!("node was already attached");
        }

        let Some(parent) = self.inner[before].parent else {
            panic!("other node is not attached to any parent");
        };

        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        }

        let before_prev = replace(&mut self.inner[before].siblings[0], Some(node));

        {
            let node_data = &mut self.inner[node];
            node_data.parent = Some(parent);
            node_data.siblings = [before_prev, Some(before)];
        }

        match before_prev {
            Some(prev) => self.inner[prev].siblings[1] = Some(node),
            None => self.inner[parent].children[0] = Some(node),
        }
    }

    pub fn attach_node_after(&mut self, node: NodeIndex, after: NodeIndex) {
        if self.inner[node].parent.is_some() {
            panic!("node was already attached");
        }

        let Some(parent) = self.inner[after].parent else {
            panic!("other node is not attached to any parent");
        };

        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        }

        let after_next = replace(&mut self.inner[after].siblings[1], Some(node));

        {
            let node_data = &mut self.inner[node];
            node_data.parent = Some(parent);
            node_data.siblings = [Some(after), after_next];
        }

        match after_next {
            Some(next) => self.inner[next].siblings[0] = Some(node),
            None => self.inner[parent].children[1] = Some(node),
        }
    }

    fn cycle_check(&self, node: NodeIndex, mut parent: NodeIndex) -> bool {
        // When `node` does not have any children it can't contain `parent`.
        if self.inner[node].children[0].is_none() {
            return true;
        }

        loop {
            if parent == node {
                return false;
            } else if let Some(next) = self.inner[parent].parent {
                parent = next;
            } else {
                return true;
            }
        }
    }

    pub fn detach_node(&mut self, node: NodeIndex) -> Option<NodeIndex> {
        let node_data = self.inner.node_weight_mut(node)?;
        let parent = take(&mut node_data.parent);
        let siblings = take(&mut node_data.siblings);

        if let Some(parent) = parent {
            match siblings[0] {
                Some(prev) => self.inner[prev].siblings[1] = siblings[1],
                None => self.inner[parent].children[0] = siblings[1],
            }

            match siblings[1] {
                Some(next) => self.inner[next].siblings[0] = siblings[0],
                None => self.inner[parent].children[1] = siblings[0],
            }
        }

        parent
    }

    #[inline]
    pub fn parent_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.inner.node_weight(node)?.parent
    }

    #[inline]
    pub fn first_node(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.inner.node_weight(parent)?.children[0]
    }

    #[inline]
    pub fn last_node(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.inner.node_weight(parent)?.children[1]
    }

    #[inline]
    pub fn next_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.inner.node_weight(node)?.siblings[1]
    }

    #[inline]
    pub fn prev_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.inner.node_weight(node)?.siblings[1]
    }
}

struct InnerNode<N> {
    weight: N,
    /// The first and last child of the node, if any.
    children: [Option<NodeIndex>; 2],
    parent: Option<NodeIndex>,
    siblings: [Option<NodeIndex>; 2],
}

// impl<N, E> NestedGraph<N, E> {
//     pub fn add_node(&mut self, weight: N, parent: Option<NodeIndex>) -> NodeIndex {
//         let node = self.inner.add_node(InnerNode {
//             weight,
//             child: None,
//             parent: None,
//             siblings: [NodeIndex::new(0); 2],
//         });

//         match parent {
//             Some(parent) => {
//                 let child = *self.inner[parent].child.get_or_insert(node);

//                 if child == node {
//                     self.inner[node].siblings = [node, node];
//                 } else {
//                     let sibling_prev = std::mem::replace(&mut self.inner[child].siblings[0], node);
//                     self.inner[node].siblings = [sibling_prev, child];
//                 }
//             }
//             None => {
//                 self.inner[node].siblings = [node, node];
//             }
//         }

//         node
//     }

//     pub fn node_parent(&self, node: NodeIndex) -> Option<NodeIndex> {
//         self.inner.node_weight(node)?.parent
//     }
// }
