use std::{collections::VecDeque, num::NonZeroUsize};

#[derive(Clone, Copy)]
struct Edge {
    to: u8,
    next: Option<NonZeroUsize>,
}
struct Graph {
    edges: Vec<Edge>,
    vertex: Box<[Option<NonZeroUsize>; 256]>,
    degree: Box<[u32; 256]>,
}
impl Graph {
    fn new() -> Self {
        Self {
            edges: Vec::new(),
            vertex: Box::new([None; 256]),
            degree: Box::new([0; 256]),
        }
    }
    fn add_edge(&mut self, from: u8, to: u8) {
        self.edges.push(Edge {
            to,
            next: self.vertex[from as usize],
        });
        self.vertex[from as usize] = Some(unsafe { NonZeroUsize::new_unchecked(self.edges.len()) });
        self.degree[to as usize] += 1;
    }
}

pub fn recover_secret(triplets: Vec<[char; 3]>) -> String {
    let mut graph = Graph::new();
    for t in triplets {
        graph.add_edge(0, t[0] as u8);
        graph.add_edge(t[0] as u8, t[1] as u8);
        graph.add_edge(t[1] as u8, t[2] as u8);
    }

    let mut queue = VecDeque::new();
    let mut ret = String::new();
    queue.push_back(0);

    while let Some(v) = queue.pop_front() {
        if v != 0 {
            ret.push(v as char);
        }

        let mut p = graph.vertex[v as usize];
        while let Some(e) = p {
            let edge = graph.edges[e.get() - 1];
            graph.degree[edge.to as usize] -= 1;
            if graph.degree[edge.to as usize] == 0 {
                queue.push_back(edge.to);
            }
            p = edge.next;
        }
    }

    ret
}
