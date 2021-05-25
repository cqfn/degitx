# Summary
A big enterprise sometimes has a large number of developers. In some extreme cases there might be up to 100,000 developers worldwide, with the majority of these developers concentrating in one country. Managing the repositories for the big enterprise can be really challenging, considering that there might be over 1,000,000 repositories and a few billion lines of the code in total. In the example customer we interviewed, they built a customized git management system named GitPortal based on GitLab community. 

# Git Management System Usage
* Developers interact with Git repositories through Git Portal Page.  These activities include opening the web pages on Git Portal, issuing common git commands such as git fetch and push, conducting code reviews, and creating merge requests.  The number of requests sent to the Git Portal Site can be quite a lot.  
* There are other developer tools and services depending on Git Management System. For example, IDE can communicate with Git Portal to display the information of repositories, or developer analytics systems may collect development activity metrics for reporting.  We estimate that the number of requests can be 10,000 per minute. 
* CI system issues git fetch immediately and runs many preconfigured tasks after the developers create a merge request. The huge number of git fetch commands could introduce the issue of bandwidth saturation.  In rare cases, a merge request to one git repository can trigger the downloading hundreds of repositories in CI system for verification. Multiple of such tasks can be executed concurrently.  
* The single repository may hold a large number of code. Based on one research, we find the size in more than 1% of repositories can be larger than 5GB and some of them can be over 20GB.  These large repositories may store millions of git objects.  One request of git fetch can consume 20-30 GB disk traffic and IOPS of disk often peaks. 

# GitLab Problem Statement
As we know, Gitlab is designed as a distributed system that runs lots of gitaly servers to support git operations of many repositories. All git operations are dispersed to different gitaly servers and each server will not have too high number of requests.

However the limited number of requests in each gitaly does not necessarily mean each request can be returned quickly. If there are too many requests for the same git repository, Gitlab can route the requests to different gitaly servers, but all the git operations will access from the same disk server. Gitaly architecture does not support distributing a single git reopsitory’s operations to different disk servers. A single disk server has IOPS limit, therefore too many IOPS will cause the disk to stop serving, which can happen if too many git fetch operations for the repository happen simultaneously, or the repository has too many git objects which take huge disk size.	

The new version of gitaly proposed a new design for a service which claims to provide strong consistency, but in fact it doesn’t provide linear-ability of commands in the system. GitLab requires a licensing fee for HA features and customer support. The license can be revoked in certain conditions. 

# Functional Requirements	
##  gRPC interfaces of gitaly version 1.27.1
The new DeGitX is expected to be compatible with the gitaly version 1.27.1. The Git Management system currently built on GitLab v11.9.9 can switch from gitaly v1.27.1 to DeGitX seamlessly.  DeGitX should not change the fact that Gitlab (frontend) keeps routing information of git repositories in a database.  DeGitX may have its own metadata of git repositories but it is different with Gitlab’s. 
##  Storage replication for a specific git repository
Because of the bottleneck of disk IOPS, DeGitX should support distributed storage for any git repository. We need storage replicas to support a large number of read requests on one git repository. 	
* **Strong Write consistency Git Management System** such as GitLab or GitHub interact with a git repository using various commands such as create, delete, update a branch/tag, create, update a merge request, migrate its position. DeGitX must support strong write consistency for multiple replicas of a repository. Consensus could be implemented using Raft or Paxos algorithm.			
* **Control interfaces (API) for replicas** most git repositories are accessed by a small team from one geographical region so there is no need to manage a storage replica in a different region. Many git repositories are not active so there is no need to create storage replicas. We suggest that by default a new repository is created without any replica. Degitx should provide control interfaces to support the administrator create/update/delete storage replicas for a git repositories in any geographical region supported in the system.
* **Route git clients to usable active replicas** DeGitX should provide a proxy the client sends read requests to one of the active replicas that has the newest content at that moment. So degitx need to keep metadata of all the replicas especially if the git content is newest of not. (Don’t need to worry about it) 
* **Git Garbage Collection** if git repository has too many unused objects or packages, git operations will need more IOPS and take longer time. DeGitX shall have provide a garbage collection to detect the status of git repositories and delete these unused repositories.

## Collect Performance Data and Reporting / Support Metrics Interface
DeGitX shall collect metrics from the repositories and git operation information.	
* **disk space usage** administrator can do jobs such as adding new disks, migrating repositories from one disk to another according to the disk space usage.
* **disk read and write speed** degitx should continuously detect the read and write speed of disks. One is to detect faulty disks. The other is to perform manual intervention to optimize storage content if the read and write speed is affected by IOPS.	
* **git operations** falling on a specific disk degitx should continuously de- tect the git operations falling on a specific disk, if a disk always undertake more git fetchs on average than other disks, then the administrator may consider adding replicas for some repositories on it.
* **time consumed by git operation** the time consumed by the operation can reflect problems such as the need to do git gc or the repository is too large.
* **request numbers for each git repository** The more active a repository is, the more needs for storage replicas. 

# Non-functional Requirements 
* **Read scalability** The solution should scale out the read capacity of a system, each region should be able to access the repository using most available replica nodes. 
* **Strong consistency** All? (TODO: discuss, maybe not all but the majority of replicas) active replica repositories should be synchronized on updates in any node with immediate consistency. Durability 
* **Durability**: The system must have enough replicas to recover itself in case of corruption. Corrupted repository could be responsible for recovering itself using replica nodes. 
* Self management (rename?) Self service, or automatic operation.  Each node performs cleanup when needed (git gc) and may remove replicas from storage on read inactivity. A node should be able to find and synchronize new repositories on read, after that it should be up to date on new updates. 
* **Maintainability** Node administrator can change the storage, and perform data migration from one storage to another. Repository administrators are able to add or delete nodes for new regions and get all nodes status for the repository. 
* **Audibility** Node doesn’t perform access control operations, but logs all requests with identity and performed operation. 
* **Analytics** Node collects statistics for each repository and usage metrics, such as push and pull operations, etc. The system keeps the whole statistics about nodes, e.g. how many nodes contains each repository, the state of nodes.
* **Exception Handling vs Monitoring & Logging**: collect the data related to the following signals: 
  * Latency of success and failed requests
  * Traffic: http request per second, network I/O rate
  * Errors: http 500, error messages from application logs
  * Saturation: memory usage, I/O, CPU and Storage 