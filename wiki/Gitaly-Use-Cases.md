# Git push over ssh
## Summary
* client runs 'git push'
* client's git starts up remote git-receive-pack on server 
* client git negotiates refs 
* client git sends packfile data
* client git sends ref update
* server updates ref
  * this has hooks, which gitlab relies on, crucially
      * pre-receive hook  (write packfile in the temp quarantine directory.  Gitaly calls back gitlab and gitlab use gRPC to call gitaly to check like restrictive branch) HA could be a challenge. 
      * update hook 
      * git-receive-pack does the actual update
      * post-receive hook.  (Call backs to trigger gitlab CI) 

## per session
* git client connects to gitlab via ssh,
* sshd spawns gitlab-shell
* gitlab-shell parses original ssh command and make API call to /api/v4/internal
* API response with: 
  * gitaly address
  * gitaly authentication token
  * repository objects such as storage name, relative path
  *  callback information such as logial username GL_ID, logical project name GL_REPOSITORY)
* gitlab-shell uses this metadata to establish SSHReceivePack session
* gitaly spawn 'git receive-pack' in the right repository directory, with environment variables GL-ID and GL_REPOSITORY

## git session 
* git client send git pack data
* ssh client ships to ssh server
* ssh server copies to stdin of gitlab-shell
* gitlab-shell packages data into protobuf message 
* protobuf message goes across gRPC connection to gitaly 
* gitaly server receives chunk and writes to stdin of git-receive-pack
* at the same time, git-receive-pack on server prints status information to stderr and stdout 
* status information get proxied back all the way to git client 

## after pack data is sent
* git-receive-pack tries to update refs
* hooks run
* hooks make pre-receive checks (g.g. to block force push, for protected branches, ...) 
  * make HTTP callback request to rails
* on success, git-receive pack prints some messages and exit with 0
* gitlab-shall exits with 0
* git client knows push is done

# Git clone 
* user runs git clone https://github.com/....git
* git makes HTTP request: GET https://github.com...git/info/refs&service=git-upload-pack
* git on server returns list of all references
* git on client picks what refs/ commints it wants to have
* git client makes HTTP request: POST https://github.com/...git/git-upload-pack
** POST body: description of "wants"
** POST RESPONSE: packfile with the requested objects and a ref update description