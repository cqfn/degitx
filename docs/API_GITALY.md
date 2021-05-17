## API Design
Gitaliy expose high-level Git operations, not low-level Git object/ref storage lookups.

Reasons:
- GitLab requests should use as few Gitaly gRPC calls as possible.
- Defining new gRPC calls is cheap. It is better to define a new 'high level' gRPC call and save gRPC round trips than to chain / combine 'low level' gRPC calls.
- Many interesting Git operations involve an unbounded number of Git object lookups. For example, the number of Git object lookups needed to generate a diff depends on the number of changed files and how deep those files are in the repository directory structure. It is not feasible to make each of those Git object lookups a remote procedure call.

## API Implementation
Gitaly intentionally isolates Git queries in individual processes. So it doesn't use a Git library like [git2go](https://github.com/libgit2/git2go) or [go-git](https://github.com/src-d/go-git)

Reason:

> We could (and may) use Git libraries to make custom query executables but we seem to get by well enough with regular `git`.

see all Gitaly design decisions [here](https://gitlab.com/gitlab-org/gitaly/-/blob/master/doc/DESIGN.md#decisions)

However with [commit](https://gitlab.com/gitlab-org/gitaly/-/commit/a062f17c598c7bd91a44e480e2bc79883bc0917d) Gitaly has new gitaly-git2go command under /cmd/gitaly-git2go directory.
According to its commit message It doesn't do much except demonstrating it's possible to link against Git2Go and its bundled lbigit2 static archive and use its functionality. At a later point, this is going to be the entrypoint for any Git functionality that we want to implement via Git2Go.
Nowdays Gitaly still doesn't use git2go.

### Example:

Let's consider CommitDiff RPC from [/proto/diff.proto](https://gitlab.com/gitlab-org/gitaly/-/blob/master/proto/diff.proto)

```
rpc CommitDiff(CommitDiffRequest) returns (stream CommitDiffResponse) {
    option (op_type) = {
      op: ACCESSOR
    };
  }

```
Go implementation for CommitDiff RPC is in [internal/gitaly/service/diff/commit.go](https://gitlab.com/gitlab-org/gitaly/-/blob/master/internal/gitaly/service/diff/commit.go#L21) You can dive in code, but long story short, it execute Git queries via Go SDK Package os/exec and then parse output with a self-made parse function.
os/exec has good documentation and examples, please check it [here](https://golang.org/pkg/os/exec/).

## Table


catfile = cat-file --batch-check &  cat-file --batch

branchName = for-each-ref --format=%(refname) refs/heads

RPC | map to Git | execution way | written in
----|---|---|---
GetBlob | catfile | cmd | Go
GetBlobs | catfile  | cmd | Go
GetLFSPointers | https://git-lfs.github.com | rugged? | Go
ApplyBfgObjectMapStream | catfile & for-each-ref --format &  update-ref -z --stdin & (After https://rtyley.github.io/bfg-repo-cleaner/ OR filter-repo) | cmd | Go
CommitIsAncestor | merge-base --is-ancestor | cmd | Go
TreeEntry | catfile | cmd | Go
CommitsBetween | log --pretty=%H --reverse | cmd | Go
CountCommits | rev-list --count | cmd | Go
CountDivergingCommits | rev-list --count --left-right | cmd | Go
GetTreeEntries | catfile | cmd | Go
ListFiles | log --max-count=1 & ls-tree -z -r --full-tree --full-name | cmd | Go
FindCommit | catfile | cmd | Go
CommitStats | catfile & diff --numstat | cmd | Go
FindAllCommits | branchName & log --pretty=%H | cmd | Go
FindCommits | branchName & log & catfile | cmd | Go
CommitLanguages | branchName & rev-parse & https://github.com/github/linguist | cmd | Go
RawBlame | blame -p | cmd | Go
LastCommitForPath | catfile & log --format=%H --max-count=1 | cmd | Go
ListLastCommitsForTree | ls-tree -z --full-name & catfile & log --format=%H --max-count=1 | cmd | Go
CommitsByMessage | branchName & log --grep={inputQuery} --regexp-ignore-case | cmd | Go
ListCommitsByOid | catfile | cmd | Go
ListCommitsByRefName | catfile | cmd | Go
FilterShasWithSignatures | catfile | cmd | Go
GetCommitSignatures | catfile | cmd | Go
GetCommitMessages | catfile | cmd | Go
ListConflictFiles | ? | rugged? | Go
ResolveConflicts | ? | rugged? | Go
CommitDiff | diff --patch --raw --abbrev=40 --full-index --find-renames=30% -c diff.noprefix=false | cmd | Go
CommitDelta | diff --raw --abbrev=40 --full-index --find-renames -c diff.noprefix=false | cmd | Go
RawDiff | diff --full-index | cmd | Go
RawPatch | format-patch --stdout --signature GitLab | cmd | Go
DiffStats | diff --numstat -z
PreReceiveHook | https://gitlab.com/gitlab-org/gitaly/-/tree/master/cmd/gitaly-hooks
PostReceiveHook | 
UpdateHook | 
ReferenceTransactionHook | 
WalkRepos | doesn't call git | - | -
AddNamespace | doesn't call git | - | -
RemoveNamespace | doesn't call git | - | -
RenameNamespace | doesn't call git | - | -
NamespaceExists | doesn't call git | - | -
CreateObjectPool | clone --quiet --bare --local & config | cmd | Go
DeleteObjectPool | doesn't call git | - | -
LinkRepositoryToObjectPool | init --bare | cmd | Go
UnlinkRepositoryFromObjectPool | remote remove | cmd | Go
ReduplicateRepository | repack --quiet -a | cmd | Go
DisconnectGitAlternates | fsck --connectivity-only | cmd | Go
FetchIntoObjectPool | remote & remote (set-url or add) & fetch --quiet & pack-refs --all & count-objects --verbose | cmd | Go
GetObjectPool | doesn't call git | - | -
UserCreateBranch | | | Go
UserUpdateBranch | | | Go (with Feature flag)
UserDeleteBranch | | | Go
UserCreateTag | | | Go
UserDeleteTag | | | Go
UserMergeToRef | | | Go
UserMergeBranch | | | Go (Ruby is not removed)
UserFFBranch | | | Go (Ruby is not removed)
UserCherryPick | | | Go (Ruby is not removed)
UserCommitFiles | | | Go
UserRebaseConfirmable | | | Go (with Feature flag)
UserRevert | | | Go
UserSquash | | | Go
UserApplyPatch | | | Ruby (Go version is implemented)
UserUpdateSubmodule | | | Go
RepositoryReplicas | doesn't call git | - | -
ConsistencyCheck | doesn't call git | - | -
DatalossCheck | doesn't call git | - | -
SetAuthoritativeStorage | doesn't call git | - | -
FindDefaultBranchName | branchName & rev-parse --symbolic-full-name | cmd | Go
FindAllBranchNames | for-each-ref --format=%(refname) refs/heads | cmd | Go
FindAllTagNames | for-each-ref --format=%(refname) refs/tags | cmd | Go
FindRefName | for-each-ref --format=%(refname)  --count=1 --contains | cmd | Go
FindLocalBranches | catfile | cmd | Go
FindAllBranches | catfile & for-each-ref refs/heads, refs/remotes | cmd | Go
FindAllTags | catfile for-each-ref refs/tags| cmd | Go
FindTag | catfile & tag --format | cmd | Go
FindAllRemoteBranches | catfile & for-each-ref refs/remotes/ | cmd | Go
RefExists | show-ref --verify --quiet | cmd | Go
FindBranch | for-each-ref refs/heads/ | cmd | Go
DeleteRefs | update-ref -z --stdin & for-each-ref | cmd | Go
ListBranchNamesContainingCommit | for-each-ref refs/heads | cmd | Go
ListTagNamesContainingCommit | for-each-ref refs/taga | cmd | Go
GetTagMessages | catfile | cmd | Go
ListNewCommits | rev-list --not --all & catfile | cmd | Go
ListNewBlobs | catfile & rev-list --objects --all --not | cmd | Go
PackRefs | pack-refs --all | cmd | Go
AddRemote | | | Go
FetchInternalRemote | fetch --prune (upload-pack?) --git-dir repoPath | cmd | Go
RemoveRemote | remote remove | cmd | Go
UpdateRemoteMirror | | | Ruby (Go version is implemented)
FindRemoteRepository | ls-remote "HEAD" | cmd | Go
FindRemoteRootRef | remote show | cmd | Go
ListRemotes | remote -v | cmd | Go
ServerInfo | doesn't call git | - | -
DiskStatistics | doesn't call git | - | -
InfoRefsUploadPack | upload-pack --stateless-rpc --advertise-refs | cmd | Go
InfoRefsReceivePack | receive-pack --stateless-rpc --advertise-refs | cmd | Go
PostUploadPack | upload-pack -c uploadpack.allowFilter=true -c uploadpack.allowAnySHA1InWant=true --stateless-rpc | cmd | Go
PostReceivePack | receive-pack -c receive.fsck.badTimezone=ignore -c core.alternateRefsCommand=exit 0 # -c core.hooksPath=hooks.Path --stateless-rpc | cmd | Go
SSHUploadPack | upload-pack -c uploadpack.allowFilter=true -c uploadpack.allowAnySHA1InWant=true | cmd | Go
SSHReceivePack | receive-pack -c receive.fsck.badTimezone=ignore -c core.alternateRefsCommand=exit 0 # -c core.hooksPath=hooks.Path | cmd | Go
SSHUploadArchive | upload-archive | cmd | Go
VoteTransaction | doesn't call git | - | -
WikiGetPageVersions | | | Ruby
WikiWritePage | | | Ruby
WikiUpdatePage | | | Ruby
WikiDeletePage | | | Ruby
WikiFindPage | | | Ruby
WikiFindFile | | | Ruby
WikiGetAllPages | | | Ruby
WikiListPages | | | Ruby
RepositoryExists | doesn't call git | - | -
RepackIncremental | repack (4x -c from config) -d | cmd | Go
RepackFull | repack (4x -c from config) -d -A --pack-kept-objects -l | cmd | Go
GarbageCollect | worktree remove --force & worktree prune & update-ref & gc & config core.commitGraph=true & commit-graph write --reachable & count-objects --verbose | cmd | Go
WriteCommitGraph | commit-graph write --reachable | cmd | Go
RepositorySize | du -sk | cmd | Go
ApplyGitattributes | catfile | cmd | Go
FetchRemote | | | Go
CreateRepository | init --bare --quiet / cmd / Go
GetArchive | archive | cmd | Go
HasLocalBranches | for-each-ref --count=1 refs/heads | cmd | Go
FetchSourceBranch | upload-pack --git-dir fetch --prune | cmd | Go
Fsck | --git-dir & fsck | cmd | Go
WriteRef | symbolic-ref & update-ref -z --stdin | cmd | Go
FindMergeBase | merge-base | cmd | Go
CreateFork | clone --bare --no-local & remote remove origin & init --bare --quiet| cmd | Go
IsRebaseInProgress | doesn't call git | - | -
IsSquashInProgress | doesn't call git | - | -
CreateRepositoryFromURL | clone --bare --quiet -c http.followRedirects=false & init --bare --quiet & remote remove origin| cmd | Go
CreateBundle | worktree remove --force & worktree prune | cmd | Go
CreateRepositoryFromBundle | clone --bare --quiet & fetch --quiet refs/*:refs/* & init --bare --quiet | cmd | Go
SetConfig | | | Ruby
DeleteConfig / config --unset-all | cmd | Go
FindLicense | | | Ruby (Go version is implemented)
GetInfoAttributes | doesn't call git | - | -
CalculateChecksum | show-ref --head | cmd | Go
Cleanup | worktree remove --force & worktree prune | cmd | Go
GetSnapshot | doesn't call git | - | -
CreateRepositoryFromSnapshot | doesn't call git | - | -
GetRawChanges | catfile & diff --raw -z | cmd | Go
SearchFilesByContent | grep ... | cmd | Go
SearchFilesByName | ls-tree --full-tree --name-status -r | cmd | Go
RestoreCustomHooks | tar -xf - -C | cmd | Go
BackupCustomHooks | tar -c -f - -C | cmd | Go
FetchHTTPRemote | Unimplemented | - | -
GetObjectDirectorySize | doesn't call git | - | -
CloneFromPool | clone --bare --shared + Ruby | cmd + ? | Go + Ruby
CloneFromPoolInternal | clone --bare --shared & fetch --prune (upload-pack?) --git-dir repoPath | cmd | Go
RemoveRepository | doesn't call git | - | -
RenameRepository | doesn't call git | - | -
ReplicateRepository | init --bare --quiet & tar -C -xvf - | cmd | Go
OptimizeRepository | repack -A --pack-kept-objects -l -d | cmd | Go

## Related issues for under development ruby/go RPCs

gRPC | Feature Flag | Go | Ruby | related issue/MR
----|---|---|---|---
ListConflictFiles | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/326
ResolveConflicts | going to be removed | + | + (going to be removed) | https://gitlab.com/gitlab-org/gitaly/-/issues/3289
UserCreateBranch | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3412
UserUpdateBranch | going to be removed | + | + (going to be removed) | https://gitlab.com/gitlab-org/gitaly/-/issues/3472
UserDeleteBranch | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3370
UserCreateTag | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3413
UserDeleteTag | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3371
UserMergeToRef | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3270
UserMergeBranch | removed (go vers is used) | + | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3217
UserFFBranch | removed (go vers is used) | + |  + (going to be removed) | https://gitlab.com/gitlab-org/gitaly/-/issues/3267
UserCherryPick | removed (go vers is used) | + |  + (going to be removed) | https://gitlab.com/gitlab-org/gitaly/-/issues/3281
UserCommitFiles | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3458
UserRebaseConfirmable | + (go vers by default) | + | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3575
UserRevert | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3347
UserSquash | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3258
UserApplyPatch | not added | + (going to be merged in master) | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3076
UserUpdateSubmodule | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3290
AddRemote | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/1465
UpdateRemoteMirror | + (ruby default) | + | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3522
FetchRemote | removed (ported on go) | + | - | https://gitlab.com/gitlab-org/gitaly/-/issues/3307
**SetConfig** | - | - | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3029
FindLicense | going be added to master | + (going be added to master) | + | https://gitlab.com/gitlab-org/gitaly/-/issues/3078

Also Wiki service RPCs are currently on Ruby.


