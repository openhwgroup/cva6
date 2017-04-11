# Synthesis Results

## Scoreboard

Synthesized @ 0.4 ns, typical case, UMC65:

|    **Type**   | **Flip-flop based, 8 entries** | **Latch based, 8 entries** | **Latch based, 4 entries** |
|---------------|--------------------------------|----------------------------|----------------------------|
| Sequential    | 18125                          | 11620                      | 6649                       |
| Combinatorial | 27333                          | 20821                      | 9438                       |
| Buffer        | 1863                           | 1000                       | 594                        |
| **Total**     | **45568 (~32 kGE)**            | **32441 (~23 kGE)**        | **16088 (~ 11 kGE)**       |


## ALU

|    **Type**   | **1.6 ns, worst case, UMC65** |
|---------------|-------------------------------|
| Sequential    | 0                             |
| Combinatorial | 9019                          |
| Buffer        | 582                           |
| **Total**     | **9019 (~6.4 kGE)**           |


w