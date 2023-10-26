# Chiquito vs Halo2

There are two major architectural differences between Chiquito and Halo2:

- Chiquito circuit is composed of “step” instances. Each step type defines the constraints among witnesses, fixed columns, and lookup tables. Step instances are also called “super rows”, each composed of one or multiple rows in a PLONKish table. We made this design choice to allow for more complex constraints, which sometimes require allocating multiple Halo2 rows.
- Chiquito DSL is based on “signals” rather than columns in order to abstract away column placements. One signal can be placed in different columns across different steps, all handled by Chiquito’s compiler.

Chiquito circuit has the following architecture

- Circuit
    - Setup
		- Forward signals
		- Shared signals
		- Fixed signals
    	- Step types
			- Setup
				- Internal signals
        		- Constraints
        		- Transition constraints
				- Lookup
        	- Witness generation
    - Trace