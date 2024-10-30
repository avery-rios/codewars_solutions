This challenge was inspired by [this kata](https://www.codewars.com/kata/63306fdffa185d004a987b8e). You should solve it before trying this harder version.
# The room

The situation regarding the lights and the switches is exactly is the same as in the original kata. Here is what you should know :

You are in a room with `n` lights indexed from `0` to `n-1` and `m` light switches indexed from `0` to `m-1`. All of the lights are initially off. Each of the switches is linked to some (or none) of the lights. When you toggle a switch, each of the lights to which it is linked changes its state from on to off or off to on.

The links between the switches and the lights are described by an array `corresponding_lights_list` of size `m`, whose element of index `i` is the list of the lights the switch `i` is linked to.

Here is an example :
```
[
  [0, 1, 2],    // switch 0 controls lights 0, 1, 2
  [1, 2],       // switch 1 controls lights 1, 2
  [1, 2, 3, 4], // switch 2 controls lights 1, 2, 3, 4
  [1, 4]        // switch 3 controls lights 1, 4
]
```
In this example toggling the switch `0` will turn on the lights `0`, `1`, and `2`. After this toggling the switch `3` will turn off the light `1` and turn on the light `4` 


## Your task

Your new goal in this kata is, given the relationships between lights and switches, and a choice of lights that you want to turn on, to check if it possible to turn <u>only</u> those lights on, and when it is, to find which switches should be toggled to do so.

Better yet, you will implement this by writing a function that as an input takes the two-dimensional array representing relationships between lights and switches, and creates a controller object that can quickly tell if any choice of lights is possible and which switches to toggle.

More precisely:

You have to implement the type `LightController` with the constructor 
```rust
new(n: usize, corresponding_lights_list: &[Vec<usize>]) -> Self
```
```python
__init__(self, n: int, corresponding_lights_list: list[list[int]]) -> None
```
and the solve method
```rust
solve(&self, lights: &Vec<usize>) -> Option<Vec<usize>>
```
```python
solve(self, lights: list[int]) -> list[int] | None
```

where:
- `n` and `corresponding_lights_list` are defined as above
- `lights` is the sorted list of the indices of the lights that you want to turn on
- `solve` returns `None` if the choice of lights is impossible to reach, and when possible the list of the indices of the switches to toggle.

During the tests, about a dozen of controllers of significant size will be instanciated. `n` and `m` will grow up to ~500 depending on the language. For each of those controllers up to 3000 lights choices can be provided for solving. Make sure the redundant computations are done at the creation of the controller!

Your controller should also be able to handle all the possible cases. A light may be linked to no switch, a switch may be linked to no light, there may be no switches or even no lights. You may also just want to be in the dark and let all the lights off...

