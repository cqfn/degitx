# System Design Overview in One Single Region Deployment

The frontend server will offer the same gRPC APIs that are fully compatible with Gitaly, to serve three different clients:
1. gitlab-shell
2. gitlab-workhorse
3. gitlab-web
4. In additional the three original clients above, a new client named ops web will be developed for the administration jobs and data analysis. 

## Front End Server (FES)
Not only does FES provide the gPRC interface, but also it enforces the strong consistency by using the database and etcd.  Git Hooks are implemented to keep the communication between FES and the Back End Server (BES)   

Wwe need FES provide some gRPC interface to do some administration jobs, such like:

```
// CreateRepositoryReplicas creates replicas of a specific repository
rpc CreateRepositoryReplicas(CreateRepositoryReplicasRequest) returns (CreateRepositoryReplicasResponse)

// RemoveRepositoryReplicas remove replica(s) of a specific repository
rpc RemoveRepositoryReplicas(RemoveRepositoryReplicasRequest) returns (RemoveRepositoryReplicasResponse)

// GetRepositoryReplicas returns replicas informations of a specific repository
rpc GetRepositoryReplicas(GetRepositoryReplicasRequest) returns (GetRepositoryReplicasResponse)

// SyncronizeRepositoryReplicas will lock all write actions and syncronize all replicas at once
rpc SyncronizeRepositoryReplicas(SyncronizeRepositoryReplicasRequest) returns (SyncronizeRepositoryReplicasResponse)

// RemoveRepository removes the repository and all replicas from the system
rpc RemoveRepository(RemoveRepositoryRequest) returns (RemoveRepositoryResponse)
```

## Back End Server (BES)
BES executes git operations including git push, git pull, etc.  Reference-transaction hooks might be the most critical operation implemented by BES

[[/images/chao/deployment.png]]

# Call Sequences for Various Git Operations
## Create Repository 
[[images/chao/seq_create_repo.png | Create Repo Sequence]]

When the new repo is first created, the FES will only create one replica by default.  Immediately after the success of the first replica creation, the checksum will be calculated and saved to the metadata database, as show in the table above.  

## Add Repository Replicas
[[images/chao/seq_add_replicas.png | Add More Replicas]]

It is possible to add more replicas after the repository is created.  This operation will lock the entire repo before adding any new replicas, which is done by `calling git clone --mirror`. 

## git push 
[[images/chao/seq_push.png || git push]]

## git fetch
[[images/chao/seq_fetch.png || git fetch]]
