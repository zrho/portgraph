use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use portgraph::{graph::Graph, Direction, PortGraph};

fn make_line_graph(size: usize) -> Graph<usize, (usize, usize, usize)> {
    let mut graph = Graph::with_capacity(size, size * 2);
    let edge = graph.add_edge((0, 0, 1));
    let mut prev_node = graph.add_node_with_edges(0, [], [edge]).unwrap();

    for i in 1..size {
        let edge_in = graph
            .node_edges(prev_node, Direction::Outgoing)
            .next()
            .unwrap();
        let edge_out = graph.add_edge((i, i, i + 1));
        let node = graph.add_node_with_edges(i, [edge_in], [edge_out]).unwrap();
        prev_node = node;
    }

    graph
}

fn make_line_hypergraph(size: usize) -> PortGraph<usize, usize, usize> {
    let mut graph = PortGraph::with_capacity(size, size, size * 2);
    let mut prev_node = graph.add_node_with_ports(0, [0, 1]);

    for i in 1..size {
        let node = graph.add_node_with_ports(i, [i, i + 1]);
        let edge = graph.add_edge(i);
        graph.connect(graph.node_ports(prev_node)[1], edge);
        graph.connect(graph.node_ports(node)[0], edge);
        prev_node = node;
    }

    graph
}

fn bench_make_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph creation");

    for size in [0, 100, 10_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("make_line_graph", size),
            &size,
            |b, size| b.iter(|| black_box(make_line_graph(*size))),
        );
        g.bench_with_input(
            BenchmarkId::new("make_line_hypergraph", size),
            &size,
            |b, size| b.iter(|| black_box(make_line_hypergraph(*size))),
        );
    }
    g.finish();
}

fn bench_clone_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph cloning");

    for size in [0, 100, 10_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("clone_line_graph", size),
            &size,
            |b, size| {
                let graph = make_line_graph(*size);
                b.iter(|| black_box(graph.clone()))
            },
        );
        g.bench_with_input(
            BenchmarkId::new("clone_line_hypergraph", size),
            &size,
            |b, size| {
                let graph = make_line_hypergraph(*size);
                b.iter(|| black_box(graph.clone()))
            },
        );
    }
    g.finish();
}

criterion_group!(benches, bench_make_portgraph, bench_clone_portgraph);
criterion_main!(benches);
