use std::iter::FusedIterator;
use std::mem::{replace, take};

use crate::memory::map::SecondaryMap;
use crate::NodeIndex;

#[derive(Debug, Clone, Default)]
pub struct Layout {
    data: SecondaryMap<NodeIndex, NodeData>,
}

impl Layout {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn attach_node_last(&mut self, node: NodeIndex, parent: NodeIndex) {
        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        } else if self.data[node].parent.is_some() {
            panic!("node was already attached");
        }

        self.data[node].parent = Some(parent);
        self.data[parent].children_count += 1;

        match replace(&mut self.data[parent].children[1], Some(node)) {
            Some(prev) => self.data[prev].siblings[1] = Some(node),
            None => self.data[parent].children[0] = Some(node),
        }
    }

    pub fn attach_node_first(&mut self, node: NodeIndex, parent: NodeIndex) {
        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        } else if self.data[node].parent.is_some() {
            panic!("node was already attached");
        }

        self.data[node].parent = Some(parent);
        self.data[parent].children_count += 1;

        match replace(&mut self.data[parent].children[0], Some(node)) {
            Some(next) => self.data[next].siblings[0] = Some(node),
            None => self.data[parent].children[1] = Some(node),
        }
    }

    pub fn attach_node_before(&mut self, node: NodeIndex, before: NodeIndex) {
        if self.data[node].parent.is_some() {
            panic!("node was already attached");
        }

        let Some(parent) = self.data[before].parent else {
            panic!("other node is not attached to any parent");
        };

        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        }

        self.data[parent].children_count += 1;
        let before_prev = replace(&mut self.data[before].siblings[0], Some(node));

        {
            let node_data = &mut self.data[node];
            node_data.parent = Some(parent);
            node_data.siblings = [before_prev, Some(before)];
        }

        match before_prev {
            Some(prev) => self.data[prev].siblings[1] = Some(node),
            None => self.data[parent].children[0] = Some(node),
        }
    }

    pub fn attach_node_after(&mut self, node: NodeIndex, after: NodeIndex) {
        if self.data[node].parent.is_some() {
            panic!("node was already attached");
        }

        let Some(parent) = self.data[after].parent else {
            panic!("other node is not attached to any parent");
        };

        if !self.cycle_check(node, parent) {
            panic!("attaching the node would introduce a cycle");
        }

        self.data[parent].children_count += 1;
        let after_next = replace(&mut self.data[after].siblings[1], Some(node));

        {
            let node_data = &mut self.data[node];
            node_data.parent = Some(parent);
            node_data.siblings = [Some(after), after_next];
        }

        match after_next {
            Some(next) => self.data[next].siblings[0] = Some(node),
            None => self.data[parent].children[1] = Some(node),
        }
    }

    fn cycle_check(&self, node: NodeIndex, mut parent: NodeIndex) -> bool {
        // When `node` does not have any children it can't contain `parent`.
        if self.data[node].children[0].is_none() {
            return true;
        }

        loop {
            if parent == node {
                return false;
            } else if let Some(next) = self.data[parent].parent {
                parent = next;
            } else {
                return true;
            }
        }
    }

    pub fn detach_node(&mut self, node: NodeIndex) -> Option<NodeIndex> {
        let Some(node_data) = self.data.get_mut(node) else {
            return None;
        };

        let parent = take(&mut node_data.parent);
        let siblings = take(&mut node_data.siblings);

        if let Some(parent) = parent {
            self.data[parent].children_count -= 1;

            match siblings[0] {
                Some(prev) => self.data[prev].siblings[1] = siblings[1],
                None => self.data[parent].children[0] = siblings[1],
            }

            match siblings[1] {
                Some(next) => self.data[next].siblings[0] = siblings[0],
                None => self.data[parent].children[1] = siblings[0],
            }
        }

        parent
    }

    pub fn detach_children(&mut self, node: NodeIndex) {
        let Some(node_data) = self.data.get_mut(node) else {
            return;
        };

        node_data.children_count = 0;
        let mut child_next = node_data.children[0];

        while let Some(child) = child_next {
            let child_data = &mut self.data[child];
            child_data.parent = None;
            let siblings = take(&mut child_data.siblings);
            child_next = siblings[1];
        }
    }

    #[inline]
    pub fn parent_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.data[node].parent
    }

    #[inline]
    pub fn first_node(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.data[parent].children[0]
    }

    #[inline]
    pub fn last_node(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.data[parent].children[1]
    }

    #[inline]
    pub fn next_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.data[node].siblings[1]
    }

    #[inline]
    pub fn prev_node(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.data[node].siblings[1]
    }

    #[inline]
    pub fn node_children(&self, node: NodeIndex) -> NodeChildren<'_> {
        let node_data = &self.data[node];
        NodeChildren {
            layout: self,
            next: node_data.children[0],
            prev: node_data.children[1],
            len: node_data.children_count as usize,
        }
    }
}

#[derive(Debug, Clone, Default)]
struct NodeData {
    /// The first and last child of the node, if any.
    children: [Option<NodeIndex>; 2],
    /// The number of children
    children_count: u32,
    /// The parent of a node, if any.
    parent: Option<NodeIndex>,
    /// The sibilings of a node, if any.
    siblings: [Option<NodeIndex>; 2],
}

pub struct NodeChildren<'a> {
    layout: &'a Layout,
    next: Option<NodeIndex>,
    prev: Option<NodeIndex>,
    len: usize,
}

impl<'a> Iterator for NodeChildren<'a> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.next.unwrap();
        self.next = self.layout.next_node(current);
        Some(current)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> DoubleEndedIterator for NodeChildren<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.prev.unwrap();
        self.prev = self.layout.next_node(current);
        Some(current)
    }
}

impl<'a> ExactSizeIterator for NodeChildren<'a> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> FusedIterator for NodeChildren<'a> {}
