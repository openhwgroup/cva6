# Failed Test Report

## VMA Tests

* test_1498676631701:
	* Found bug in misaligned exception of half word access when another LSU request was incoming

* test_1498880354372:
    * Found bug in `sfence.vma`, pipeline wasn't flushing due to wrong assignment on the no store pending signal, coming from the store buffer
    * Found bug in accidental exception taken in the MMU: Even though the LSU didn't place a request on the MMU the MMU was propagating a misaligned exception signal. The solution was masking it by the `lsu_req` signal.
