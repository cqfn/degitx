## Introduction

When developing DegitX, we will maintain the performance measurement of various git operations when introducing the new design and new implementation. Specifically, Degitx supports the strong consistency of the git repository. We shall measure git push when each repository may have zero or multiple replicas as requested by the teams.  

## Comparison to Existing Solutions
### GitHub did _git clone_ performance benchmark

Back in 2015 GitHub.com and GitHub Enterprise tested the all-important git clone operation with a simple yet effective solution: a script that could run a series of simultaneous git clone commands against an Enterprise server.  https://github.blog/2015-07-22-benchmarking-github-enterprise/

The benchmark script cloned data over HTTPS or SSH and against the github/gitignore repository. The repository was picked because it is pretty small yet still has some realistic activity. In the benchmark we ramped up the number of concurrent clones over time in order to see how the VM handled heavier and heavier load. This also served as a way to determine the amount of load the benchmark script itself could generate running from a single client. After each clone, our script would output a timestamp with the start time, duration of the operation, and exit status of the clone. 

***Git Clone Over HTTPS against GitHub.com**
             
| Number of concurrent requests | # Git Operation/s| Response Time P25 | Response Time p75 | Response Time P99 | 
|-------------------------------|------------------|-------------------|-------------------|-------------------|
|           12                  |        25        | 1                 |100 ms             |300 ms             |
|           36                  |        65        | 220 ms            |300 ms             |600 ms             |
|          108                  |        80        | 1s                |1.1s               |1.2s               |
|          228                  |        55        | 2s                |3s                 |8s                 | 


### DeGitX Benchmark Objectives
1. Git Fetch
10M, 200 objects, and in the same region.  Replicas are 0, 3, 5 respectively in three rows below. 

| Number of concurrent requests | Response Time P50 | Response Time p90 | Response Time P99 | 
|-------------------------------|-------------------|-------------------|-------------------|
|           50                  | 5s                |10 s               |50s                |
|           80                  | 5s                |10 s               |50s                |
|          100                  | 5s                |10 s               |50s                |

### GitLab Performance of fetching issues when merging 
the method MergeRequest#closes_issues is used to return the list of issues to close (as an Array of Issue instances). https://about.gitlab.com/blog/2016/02/25/making-gitlab-faster/#sts=Performance%20Monitoring%20&%20Tooling

To summarize the timings:
* A mean of around 500 milliseconds
* The 95th percentile between 1 and 1.5 seconds
* The 99th percentile between 1.5 and 2 seconds

## GitLab.com usage
handling spikes of 300,000 transactions per second. GitLab.com is reaching 60,000 connections per second.
in 2020, GitLab can have 1-2k sessions per second.

## GitHub Corner Cases in 2016
https://www.youtube.com/watch?v=f7ecUqHxD7o 
* Large repository can be 40GB+ 
* Commit History can be 500k and 20 years history
* Large number of branches and tags > 1M
* High push rate 10k+ per day
* Public repos with 100+ clients

Takeaways:
* Any call to git core is less than 1 second. Git clone Linux kernel code was reduced from over a minute to 1.63 second
* Set the limits CPU, memory, and network for any user who can use, including scripts
* Cache EVERYTHING