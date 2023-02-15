use std::fmt::Display;

use crate::{Direction, PortIndex};

use super::graph::Graph;

pub fn dot_string<'a, N, P>(graph: &'a impl Graph<'a, N, P>) -> String
where
    N: 'a + Display + Clone,
    P: 'a + Display + Clone,
{
    let mut s = String::new();

    s.push_str("digraph {\n");

    for n in graph.nodes_iter() {
        let node = graph.node_weight(n).expect("missing node");
        s.push_str(&format!("{} [label=\"{:}\"]\n", n.index(), node)[..]);
        // TODO: Port weights
        // TODO: Render hyperedges properly

        for from in graph.ports(n, Direction::Outgoing) {
            for to in graph.port_links(from) {
                if graph.port_direction(to) == Some(Direction::Incoming) {
                    add_edge_str(graph, from, to, &mut s);
                }
            }
        }
    }

    s.push_str("}\n");
    s
}

fn add_edge_str<'a, N, P>(
    graph: &impl Graph<'a, N, P>,
    from: PortIndex,
    to: PortIndex,
    dot_s: &mut String,
) where
    N: 'a + Display + Clone,
    P: 'a + Display + Clone,
{
    let from_node = graph.port_node(from).expect("missing node").index();
    let to_node = graph.port_node(to).expect("missing node").index();
    let from_offset = graph.port_offset(from).expect("missing offset");
    let to_offset = graph.port_offset(to).expect("missing offset");

    let edge_s = format!("{from_node} -> {to_node} [label=\"({from_offset}, {to_offset})\"]\n");
    dot_s.push_str(&edge_s[..])
}
