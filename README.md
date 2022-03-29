# Static Allocation for Single Robot Cloud Systems
## Paper

[Optimal Algorithm Allocation for Single Robot Cloud Systems](https://ieeexplore.ieee.org/document/9468416)

## Descriptions
The code for the paper Optimal Algorithm Allocation for Single Robot Cloud Systems 

We begin by describing the graph of all algorithms, the average execution time of each algorithm to be executed on each node, the average communication time (data transmission speed) between two adjacent node, and the constraints on memory. 

The code is designed to solve the static allocation of a fixed graph of algorithms on non-isomorphic, randomly generated architectures. The solution can be obtained using a single architecture with known constraints on memory and data transmission speed. 

The result is the solution with the lowest response time and memory requirements of the edge node (the smallest distance to the origin). 

All packages (libraries) to execute the code are included in the code.

## Requirements
Install the requirements in a R environment with `packages(pcalg,igraph,combinat,statgraph,arrangements)`.


## Citation
```
@ARTICLE{9468416,
  author={Alirezazadeh, Saeid and Alexandre, Luis},
  journal={IEEE Transactions on Cloud Computing}, 
  title={Optimal Algorithm Allocation for Single Robot Cloud Systems}, 
  year={2021},
  volume={},
  number={},
  pages={1-13},
  doi={10.1109/TCC.2021.3093489}
}
```
