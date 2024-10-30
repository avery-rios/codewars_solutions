use std::{
    collections::VecDeque,
    ops::{Index, IndexMut},
};

struct Matrix<T>(usize, Vec<T>);
impl<T> Index<(isize, isize)> for Matrix<T> {
    type Output = T;
    #[inline]
    fn index(&self, index: (isize, isize)) -> &Self::Output {
        &self.1[self.0 * index.0 as usize + index.1 as usize]
    }
}
impl<T> IndexMut<(isize, isize)> for Matrix<T> {
    #[inline]
    fn index_mut(&mut self, index: (isize, isize)) -> &mut Self::Output {
        &mut self.1[self.0 * index.0 as usize + index.1 as usize]
    }
}

pub fn path_finder(maze: &str) -> Option<u32> {
    if maze.len() == 1 {
        return Some(0);
    }

    let (maze, n) = {
        let mut ret = Vec::with_capacity(maze.len());
        let mut n = None;
        for (idx, c) in maze.chars().enumerate() {
            match c {
                '.' => ret.push(true),
                'W' => ret.push(false),
                '\n' => n = n.or(Some(idx)),
                _ => unreachable!("invalid char"),
            }
        }
        let n = n.unwrap();
        (Matrix(n, ret), n)
    };
    let mut visit = Matrix(n, vec![None; n * n]);

    let mut q = VecDeque::new();
    q.push_back(((0, 0), 0));
    while let Some((cur, dist)) = q.pop_front() {
        if visit[cur].is_some() {
            continue;
        }
        visit[cur] = Some(dist);

        if cur.0 != 0 {
            let pos = (cur.0 - 1, cur.1);
            if maze[pos] {
                q.push_back((pos, dist + 1))
            };
        }
        if cur.1 != 0 {
            let pos = (cur.0, cur.1 - 1);
            if maze[pos] {
                q.push_back((pos, dist + 1))
            }
        }
        if cur.0 != n as isize - 1 {
            let pos = (cur.0 + 1, cur.1);
            if maze[pos] {
                q.push_back((pos, dist + 1));
            }
        }
        if cur.1 != n as isize - 1 {
            let pos = (cur.0, cur.1 + 1);
            if maze[pos] {
                q.push_back((pos, dist + 1))
            }
        }
    }

    visit[(n as isize - 1, n as isize - 1)]
}
