# Chiquito Programming Model

## ZKP as trace

ZKP generates proofs that an algorithm has been executed correctly.

The best way we can analyse a particular execution of an algorithm is by its trace.

For example:

```python=
def bubbleSort(arr):
	n = len(arr)
	
	for i in range(n-1):
		for j in range(0, n-i-1):

			if arr[j] > arr[j + 1]:
				arr[j], arr[j + 1] = arr[j + 1], arr[j]
```

A trace for a particular input is the actual steps that are executed in order.

For example if `arr = [64, 34, 25, 12, 22, 11, 90]`, the trace is:

```
set n to length of arr which is 7
set i to 1
set j to 0
compare arr[j] > arr[j+1] => arr[0] > arr[1] => 64 > 34 => true
set arr[0] to arr[1] and arr[1] to arr[0] => arr[0] = 34, arr[1] = 64
// and so on...
```

It is important to understand that each step has a pre-state, with the values of the variables before the execution of the step, and a post-state with the values of the variables after the execution of the step. The post-state of a step is the pre-state of the next one.

If we include the states indented:
```
	arr = [64, 34, 25, 12, 22, 11, 90]
	n = ?, i = ?, j = ?
set n to length of arr which is 7
	arr = [64, 34, 25, 12, 22, 11, 90]
	n = 7, i = ?, j = ?
set i to 1
	arr = [64, 34, 25, 12, 22, 11, 90]
	n = 7, i = 1, j = ?
set j to 0
	arr = [64, 34, 25, 12, 22, 11, 90]
	n = 7, i = 1, j = 0
compare arr[j] > arr[j+1] => arr[0] > arr[1] => 64 > 34 => true
	arr = [64, 34, 25, 12, 22, 11, 90]
	n = 7, i = 1, j = 0
set arr[0] to arr[1] and arr[1] to arr[0] => arr[0] = 34, arr[1] = 64
	arr = [34, 64, 25, 12, 22, 11, 90]
	n = 7, i = 1, j = 0
// and so on...
```

## ZKP circuit as a trace checker

We can see a ZKP circuit as a series of step types, and their constraints relative to the post-state and pre-state, and also potentially some internal values.

For example, we can have the step type `set $variable to $value` and the constraint would be that the post state of `$variable` should be `$value`.

## ZKP witness as a trace

In the same way, we can see the witness as the trace of a computation plus some information about the states between the steps.

The programming model in chiquito follows the idea that every zero knowledge proof represents a program (the setup), which can have many computations (the trace) that is proven for a certain input, output and intermediate values (the witness).

## Step types and step instances

A trace is made of a sequence of step instances or trace steps, that contains the data about that step instance.

Each step instance belongs to a step type. A step type contains rules (or constraints) about whether a step instance is valid in relation to its data and the data of other step instances relative to it.

Step types are part of the setup, which means that they cannot change between proofs, but this circuit can proof all possible traces, as they are part of the witness.

## Signals and rotations

Signals represent elements of the witness that have an independent value for each trace step, but in chiquito paradigm you can see them as variables on the trace steps.

Rotation refer to the capability of creating rules that involved the value of signals in other trace steps with an offset relative to the trace step, not just the value of a signal. A rotation of 0, represent the value of the signal in the same trace step, a rotation of 1 in the next step, a rotation of -1 in the previous step, in general any rotation number is possible.

## Types of signals

There are two types of signals that are shared between the step types, **forward** signals and **shared** signals. The difference is that forward signals can only rotate to the next step, while shared signals can rotate to any number of steps. However, circuits that only use forward signals are more efficient in some cases, so you should try to use only forward signals.

**Internal** signals are not shared between step types, and belong to a specific step type and cannot be rotated.

There is a special type of signal called **fixed**, that is not part of the witness and it is used to define constants.

|          | Scope            | Rotation  | Role    |
| -------- | ---------------- | --------- | ------- |
| Forward  | All step types   | Only next | Witness |
| Shared   | All step types   | Any       | Witness |
| Internal | Single step type | None      | Witness |
| Fixed    | All step types   | Any       | Setup   |

## Putting everything together
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