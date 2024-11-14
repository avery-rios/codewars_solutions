use std::collections::VecDeque;

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Direction {
    N = 3,
    W = 2,
    S = 1,
    E = 0,
}
impl Direction {
    const fn opposite(self) -> Self {
        match self {
            Self::N => Self::S,
            Self::W => Self::E,
            Self::S => Self::N,
            Self::E => Self::W,
        }
    }
}
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum State {
    U = 3 - 0,
    L = 3 - 1,
    D = 3 - 2,
    R = 3 - 3,
}
impl State {
    const fn next(self) -> Self {
        match self {
            Self::U => Self::L,
            Self::L => Self::D,
            Self::D => Self::R,
            Self::R => Self::U,
        }
    }
    const fn prev(self) -> Self {
        match self {
            Self::U => Self::R,
            Self::L => Self::U,
            Self::D => Self::L,
            Self::R => Self::D,
        }
    }
}
#[derive(Debug, Clone, Copy)]
enum Enter {
    Start,
    Move(Direction),
    Rotate,
}

type Pos = (usize, usize);
const START: i8 = -1;
const DEST: i8 = -2;

const fn index(w: usize, p: Pos, state: State) -> usize {
    ((w * p.0 + p.1) << 2) | (state as usize)
}
const fn can_go(v: u8, state: State, dir: Direction) -> bool {
    let bit = ((dir as u32) + (1 + state as u32)) & 0x3;
    (v & (1 << bit)) == 0
}

fn find_path(maze: &Vec<Vec<i8>>, length: usize, width: usize, start: Pos) -> Vec<Option<Enter>> {
    let mut enter = vec![None; width * length * 4];
    let mut q = VecDeque::with_capacity(width * length * 4);
    q.push_back((start, State::U, Enter::Start));
    while let Some((pos, state, from)) = q.pop_front() {
        {
            let idx = index(width, pos, state);
            if let Some(_) = enter[idx] {
                continue;
            }
            enter[idx] = Some(from);
        }
        let walls = match maze[pos.0][pos.1] {
            START => 0,
            DEST => break,
            v => v as u8,
        };

        let mut push_front = |pos: Pos, dir: Direction| {
            if can_go(walls, state, dir)
                && u8::try_from(maze[pos.0][pos.1])
                    .map_or(true, |v| can_go(v, state, dir.opposite()))
                && enter[index(width, pos, state)].is_none()
            {
                q.push_front((pos, state, Enter::Move(dir)));
            }
        };
        if pos.0 != 0 {
            push_front((pos.0 - 1, pos.1), Direction::N);
        }
        if pos.1 != 0 {
            push_front((pos.0, pos.1 - 1), Direction::W);
        }
        if pos.0 != length - 1 {
            push_front((pos.0 + 1, pos.1), Direction::S);
        }
        if pos.1 != width - 1 {
            push_front((pos.0, pos.1 + 1), Direction::E);
        }
        if enter[index(width, pos, state.next())].is_none() {
            q.push_back((pos, state.next(), Enter::Rotate));
        }
    }
    enter
}

fn show_path(
    width: usize,
    mut pos: Pos,
    mut state: State,
    enter: &Vec<Option<Enter>>,
) -> Vec<String> {
    let mut ret = Vec::new();
    let mut rev_str = Vec::new();

    loop {
        match enter[index(width, pos, state)].unwrap() {
            Enter::Start => break,
            Enter::Move(m) => {
                rev_str.push(match m {
                    Direction::N => b'N',
                    Direction::W => b'W',
                    Direction::S => b'S',
                    Direction::E => b'E',
                });
                pos = match m {
                    Direction::N => (pos.0 + 1, pos.1),
                    Direction::W => (pos.0, pos.1 + 1),
                    Direction::S => (pos.0 - 1, pos.1),
                    Direction::E => (pos.0, pos.1 - 1),
                }
            }
            Enter::Rotate => {
                rev_str.reverse();
                ret.push(unsafe { String::from_utf8_unchecked(rev_str) });
                rev_str = Vec::new();
                state = state.prev();
            }
        }
    }

    rev_str.reverse();
    ret.push(unsafe { String::from_utf8_unchecked(rev_str) });
    ret.reverse();
    ret
}

pub fn maze_solver(maze: &Vec<Vec<i8>>) -> Option<Vec<String>> {
    let width = maze[0].len();
    let length = maze.len();
    let (start, dest) = {
        let mut start = (0, 0);
        let mut dest = (0, 0);
        for (idx_i, i) in maze.iter().enumerate() {
            for (idx_j, j) in i.iter().enumerate() {
                match *j {
                    START => start = (idx_i, idx_j),
                    DEST => dest = (idx_i, idx_j),
                    _ => (),
                }
            }
        }
        (start, dest)
    };

    let enter = find_path(maze, length, width, start);

    let dest_state = {
        let mut ret = None;
        let base = (dest.0 * width + dest.1) << 2;
        for i in [State::U, State::L, State::D, State::R] {
            if enter[base | (i as usize)].is_some() {
                ret = Some(i);
            }
        }
        ret?
    };

    Some(show_path(width, dest, dest_state, &enter))
}

pub mod flux_puzzle {
    pub use super::maze_solver;
}
