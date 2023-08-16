# Thread Events

## Properties of concurrent objects

- wait-free: each method call finishes in finite number of steps
- lock-free: infinitely often (always eventually), some method call finishes in a finite number of steps

## Register types

Different types:

- safe, regular, atomic
- single reader (SR), single writer (SW), multiple readers (MR), multiple writers (MW)
- safe registers are not (really) safe
- boolean valued vs. M-valued

Ideas:

- write value only if distinct from previous
- going from regular/atomic to better atomic: use timestamps

## Consensus numbers

- relative power of synchronization primitives, read/write/compareAndSet
- hierarchy of synchronization primitives: maximum number of threads for which primitive can solve consensus in lock-free/wait-free way
- consensus:
  - all threads decide on the same value
  - the decided value is some thread's input (0 or 1 for binary consensus)
- valence:
  - univalent if no matter thread schedule, same decisions
  - bivalent if some pair of thread schedules differ in decisions


