Machine-generated results of the enumeration (step 4) go here. Not written by hand.

## How results reach main

The search workflow (`.github/workflows/search.yml`) ends by opening a pull request against
main itself, using the repository secret `RESULTS_PR_TOKEN` (`scripts/publish_results.sh`):

- if the commit the run started from is already in main, the merged results go onto the
  current main in a new branch `results/run-<run id>`, and the pull request changes only
  `results/` and `docs/results.md`;
- otherwise the results are committed on the run's own branch, and the pull request is that
  branch's (an already open one is reused), so it also carries the branch's unmerged commits.

A run whose token is missing, expired or lacks access stops before the search starts. A run
that is cancelled keeps its results in the artifact `results-merged` and opens no pull
request. To check the token without searching, start the workflow by hand with
`token_check_only` ticked.
