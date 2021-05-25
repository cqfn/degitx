# How to test DeGitX system

The staging environment has 10 virtual machines (TODO: specify hardware), the deployment schema for this environment is (TODO: draw deployment diagram):
 - 1 GitLab set (web, workhorse, shell) [shared instance #1]
 - 1 etcd instance for metadata storage [shared instance #1]
 - 1 round-robin load-balancer to redirect gRPC Gitlay reqeusts from GitLab to DeGitX front-end nodes [shared instance #1] 
 - 2 DeGitX front-end instances [dedicated instances #2-#3]
 - 7 DeGitX back-end instances [dedicated instances #4-10]

Supplementary services, such as GitLab services and "etcd" are deployed to single shared VM, whereas DeGitX nodes are deployed to 9 dedicated instances (2 front-end and 7 back-end).

Repositories: staging environment has 5000 repositories of different size from small (100K to 5G, average repository is 200M size), repositories are replicated and each has 3 replicas across back-end nodes.

## Test scenarios

There are multiple test scenarios to run against DeGitX system. Each test case has access to an instrumentation testing framework which includes:
 - git data generator for provided parameters (amount of commits, repository size, file size distribution, commit size distribution)
 - git client operation for GitLab shell (push and fetch)
 - GitLab API client to create or delete repositories
 - node data verification to find and verify repository replicas on back-end nodes
 - TODO: more tools


**For each test scenario, please specify what you expect for the results**

### Create and push a new repo

Scenario:
 1. Create a new repository using GitLab API   **Please add GitLab API here so it is easy to review what parameters are needed**
 2. Generate data for git repository  **What data will you generate? For example, will you add README or .gitignore by default?**
 3. Add remote to repo, push to GitLab shell
 4. Verify repository data on all replicas. **How many replicas are created and when?**

**Test Case:**  
1. If the same repository name does not exist,
>  Expected result:  
 2. If the same repository name does exist 
>  Expected result: what is the error message or error code returned from API? And step 2 - 4 shall not happen if step 1 fails.
 3. If the creation of the new repository only partially succeeds?  Can this happen? 
>  Expected result: clean up any partial data created in the process.  

### Fetch, update and push

Pre-requirements:
  - Existing repository with known git URI

Scenario:
 1. Close existing repository
 2. Update repository by generating new commit
 3. Push new changes to remote
 4. Verify all replicas for new changes

### Parallel push to different branches:

Pre-requirements:
 - Existing repository with known git URI

Configuration:
 - `C` = concurrency, amount of parallel operations

Scenario:
 1. Create `C` workspaces (directories for git repositories)
 2. Clone repository into each workspace
 3. Create new random branch in each workspace, generate random changes, commit
 4. Push changes to repository simultaneously
 5. Verify repository data on all replicas

TODO: more test cases
