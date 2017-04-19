# Synthesis Results

## Scoreboard

Synthesized @ 0.4 ns, worst case, UMC65:

|    **Type**   | **Flip-flop based, 8 entries** | **Latch based, 8 entries** | **Flip-flop based, 4 entries** | **Latch based, 4 entries** |
|---------------|--------------------------------|----------------------------|--------------------------------|----------------------------|
| Sequential    | 18125                          | 11620                      | 12143                          | 6649                       |
| Combinatorial | 27333                          | 20821                      | 19717                          | 9438                       |
| Buffer        | 1863                           | 1000                       | 2694                           | 594                        |
| **Total**     | **45568 (~32 kGE)**            | **32441 (~23 kGE)**        | **31861 (~23 kGE)**            | **16088 (~ 11 kGE)**       |


## ALU

|    **Type**   | **1.6 ns, worst case, UMC65** |
|---------------|-------------------------------|
| Sequential    | 0                             |
| Combinatorial | 9019                          |
| Buffer        | 582                           |
| **Total**     | **9019 (~6.4 kGE)**           |

## BTB

Synthesized @ 1.1 ns, worst case, UMC65

|    **Type**   |    **64 entries**   |    **32 entries**   |
|---------------|---------------------|---------------------|
| Sequential    | 4288                | 2113                |
| Combinatorial | 7901                | 5923                |
| Buffer        | 342                 | 2276                |
| **Total**     | **55490 (~39 kGE)** | **29327 (~20 kGE)** |



