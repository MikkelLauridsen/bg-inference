# Implementation of inference algorithm
This is a Haskell implementation of an inference algorithm for the type system by Baillot and Ghyselen for parallel complexity of the pi-calculus (see https://link.springer.com/chapter/10.1007/978-3-030-72019-3_3). The implementation is capable of inferring bounds of some linear time processes and many constant time processes.
The algorithm is constraint-based and as such generates constraints that we solve using the [Z3 theorem prover](https://github.com/Z3Prover/z3). The project uses [Stack](https://docs.haskellstack.org/en/stable/README/) as a build tool for Haskell.

## Prerequisites
Before building the project, the Z3 theorem prover must be installed. The implementation has been verified to work with version [4.8.12](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.12) of Z3. On Windows systems, ensure that the z3 executable is visible in PATH.

## Building using Stack
- Ensure first that the header files and library files are visible to Stack. On Windows systems this can be ensured by creating a folder named "z3-4.8.12" with subfolders "bin" and "include" containing the library and headers files, respectively.
- Install the parser generator [Happy](https://www.haskell.org/happy/#download)
- Build the project using `stack build`.

## Running
Calling the executable with a filename runs the inference algorithm on the specified file.

Example:
```
infer program.pi
```
or through stack:
```
stack run program.pi
```

Running the above with the following file program.pi present infers a correct complexity of 10.

program.pi:
```
new seq in (
    (
        *seq?(n, r).match n 
        {
            zero -> r!();
            succ(x) -> new rp in 
                ( tick.seq!(x,rp) | rp?().r!() )
        }
    ) 
    | (new r in ( seq!(10, r) | r?() ))
)
```