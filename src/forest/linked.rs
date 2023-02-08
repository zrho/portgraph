use std::iter::FusedIterator;
use std::mem::{replace, take};
use thiserror::Error;

use crate::memory::map::SecondaryMap;
use crate::memory::EntityIndex;

/// A forest of nodes using doubly linked lists.
///
/// The order of child nodes is maintained as a doubly linked list which
/// supports efficient insertion and removal at any point in the list.
#[derive(Debug, Clone)]
pub struct LinkedForest<Index> {
    data: SecondaryMap<Index, NodeData<Index>>,
}

impl<Index> LinkedForest<Index> {
    /// Creates a new empty layout.
    pub fn new() -> Self {
        Self {
            data: SecondaryMap::new(),
        }
    }
}

impl<Index> Default for LinkedForest<Index> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Index: EntityIndex> LinkedForest<Index> {
    /// Attaches a node as the last child of a parent node.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn attach_last(&mut self, node: Index, parent: Index) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
        } else if self.data[node].parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        self.data[parent].children_count += 1;
        self.data[node].parent = Some(parent);

        match replace(&mut self.data[parent].children[1], Some(node)) {
            Some(prev) => self.data[prev].siblings[1] = Some(node),
            None => self.data[parent].children[0] = Some(node),
        }

        Ok(())
    }

    /// Attaches a node as the first child of a parent node.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn attach_first(&mut self, node: Index, parent: Index) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
        } else if self.data[node].parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        self.data[parent].children_count += 1;
        self.data[node].parent = Some(parent);

        match replace(&mut self.data[parent].children[0], Some(node)) {
            Some(next) => self.data[next].siblings[0] = Some(node),
            None => self.data[parent].children[1] = Some(node),
        }

        Ok(())
    }

    /// Attaches a node before another node within the other node's parent.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///  - When the other node is a root.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn attach_before(&mut self, node: Index, before: Index) -> Result<(), AttachError> {
        if self.data[node].parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let Some(parent) = self.data[before].parent else {
            return Err(AttachError::RelativeToRoot);
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
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

        Ok(())
    }

    /// Attaches a node after another node within the other node's parent.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///  - When the other node is a root.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn attach_after(&mut self, node: Index, after: Index) -> Result<(), AttachError> {
        if self.data[node].parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let Some(parent) = self.data[after].parent else {
            return Err(AttachError::RelativeToRoot);
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
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

        Ok(())
    }

    /// Ensures that making `node` a child of `parent` would not introduce a cycle.
    fn cycle_check(&self, node: Index, mut parent: Index) -> bool {
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

    /// Detaches a node from its parent, returning the former parent.
    ///
    /// Does nothing and returns `None` when the node is a root.
    pub fn detach(&mut self, node: Index) -> Option<Index> {
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

    /// Detaches all children from a node.
    pub fn detach_children(&mut self, node: Index) {
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

    /// Returns a node's parent or `None` if it is a root.
    #[inline]
    pub fn parent(&self, node: Index) -> Option<Index> {
        self.data[node].parent
    }

    /// Returns a node's first child, if any.
    #[inline]
    pub fn first(&self, parent: Index) -> Option<Index> {
        self.data[parent].children[0]
    }

    /// Returns a node's last child, if any.
    #[inline]
    pub fn last(&self, parent: Index) -> Option<Index> {
        self.data[parent].children[1]
    }

    /// Returns the next sibling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn next(&self, node: Index) -> Option<Index> {
        self.data[node].siblings[1]
    }

    /// Returns the previous sibiling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn prev(&self, node: Index) -> Option<Index> {
        self.data[node].siblings[1]
    }

    /// Iterates over the node's children.
    #[inline]
    pub fn children(&self, node: Index) -> Children<'_, Index> {
        let node_data = &self.data[node];
        Children {
            layout: self,
            next: node_data.children[0],
            prev: node_data.children[1],
            len: node_data.children_count as usize,
        }
    }

    /// Returns the number of the node's children.
    #[inline]
    pub fn child_count(&self, node: Index) -> usize {
        self.data[node].children_count as usize
    }
}

#[derive(Debug, Clone)]
struct NodeData<Index> {
    /// The first and last child of the node, if any.
    children: [Option<Index>; 2],
    /// The number of children
    children_count: u32,
    /// The parent of a node, if any.
    parent: Option<Index>,
    /// The sibilings of a node, if any.
    siblings: [Option<Index>; 2],
}

impl<Index> Default for NodeData<Index> {
    fn default() -> Self {
        Self {
            children: Default::default(),
            children_count: Default::default(),
            parent: Default::default(),
            siblings: Default::default(),
        }
    }
}

pub struct Children<'a, Index> {
    layout: &'a LinkedForest<Index>,
    next: Option<Index>,
    prev: Option<Index>,
    len: usize,
}

impl<'a, Index: EntityIndex> Iterator for Children<'a, Index> {
    type Item = Index;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.next.unwrap();
        self.next = self.layout.next(current);
        Some(current)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, Index: EntityIndex> DoubleEndedIterator for Children<'a, Index> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.prev.unwrap();
        self.prev = self.layout.next(current);
        Some(current)
    }
}

impl<'a, Index: EntityIndex> ExactSizeIterator for Children<'a, Index> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, Index: EntityIndex> FusedIterator for Children<'a, Index> {}

#[derive(Debug, Clone, Error)]
pub enum AttachError {
    #[error("the node is already attached")]
    AlreadyAttached,
    #[error("can not attach relative to a root node")]
    RelativeToRoot,
    #[error("attaching the node would introduce a cycle")]
    Cycle,
}
