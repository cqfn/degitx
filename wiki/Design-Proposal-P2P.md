# Proposal: P2P system

The solution could be the implementation of distributed Git repository manager with strong consistent replica nodes. It guarantees high availability across different regions, durability by replicating repositories on different server racks, read scalability by routing fetch traffic to different nodes. DeGit is a peer-to-peer system, no persistent master nodes exists. Each node knows about each other due to discovery protocol. 

## From the white paper: How to create a new repository
The diagram 6 explains how administrator creates new repository with replication on predefined storage nodes by specifying its locator IDs:
1. Administrator sends request to the dashboard to create new repository R at nodes with locators L  
**Questions**: 
    * Is this a constraint that every time a developer wants to create a new repository, he/she will have to contact the administrator to create one first? **Answer**: By talking with our customers, developers shall be able to create the new repositories without the administrator.  The only exception is by default all the repositories are public, thus only the administrator can change the repository to the private. 
    * How does an administrator decide which node and which locator to create a NEW repository R? 
    * What is the relationship between Node N and Locator L?  Is it 1:1 relationship? Are they always sitting (installed) in the same VM or container? 
    * It seems that Locator is just the ID of a node.  Is it correct? If not, what else does it do? Also in Figure 3 of the white paper, plural is used for Locator(s), does it mean that there are multiple instances of Locator living inside a node? 

2. Dashboard service performs a lookup of R in metadata storage
3. Metadata storage returns locator IDs L’ of R repository if any 
**Questions**:
    * This is new repository.  The storage shall never return the locator ID L, shouldn't it? 
    * For a new repository, why do we need to identify the locator ID L for the first place?  Should we create an algorithm to identify which Node to store the new repository and then save the information to Locator L?  

4. If L’ locators are not empty, dashboard returns error to administrator. Please check the white paper, there are two numbers next to this point, 4 and 5. Please remove one. 
**Questions**
    * What does "Not Empty" mean here? It may not be the right choice of English word.  It is hard to guess here.  Do you mean if the locator for this repository does not exist, it shall return error?  

6. If no node locator is associated with repository R, then dashboard asynchronously sends requests to each node with locator ID l from list L
    * How does "asynchronously" communicate between the dashboard with other nodes? The dashboard sends the requests but how does the dashboard receive the result without waiting for the result? Do yo need a queue somewhere in the middle? 
    * This is new repository.  How does the new repository receive the list L? Does the dashboard receive the list L from the metadata store? How many elements might exist in the list L? 

7. Dashboard asks node l to start manage repository R, and specify other node locator IDs; The node l try to organize consensus between nodes L, and leader asks all other members to manage repository R
    * What happens if node l no longer responds to the dashboard at this point?  
    * What happens if node l goes down in the middle of consensus process? 

8. On success, node l updates metadata with mapping of repository R hash to node locator l
    * Can you describe what is the success here?  The majority of votes are received by the lead node l? 
9. Meanwhile, the dashboard is performing query requests to the metadata storage to get locator IDs of repository R; Metadata storage returns IDs L’.
    * In the step 7, it specifies "Dashboard asks node l to start manage repository R, and specify other node locator IDs".  So the dashboard knows node l and other locator IDs. Why does step 9 query the metadata storage again? 
10. In case if L’ is a subset of L and the size of L’ is greater or equal to half size of L plus 1 (size(L’) >= size(L)/2 + 1)
11. Dashboard finishes with success status
12. If waiting timeout is reached
13. Dashboard finishes with error status
14. Dashboard returns with success or error status to administrator

## Open Questions: (Don't worry them for now)
1. Routing rules
* How does the client locate the first locator or the first node? 
* How does the locator in each node find the other 2/3 nodes to replicate
* If the repository is not located in the local node, how can the locator/node redirect the RPC operation to the right node? 
* "_If update fails due to concurrency issue, the whole update fails_".  How does the system know the failure, and what is the concurrency issue? ... 

2. Locators
* What is locators? Where is the locator?  Is it a feature/function or a service? 
* Why does each node use public/private keys to identify instead of private keys? How these key pairs are generated by which? 
* _for issuing digital certificates for node public keys, so each node will be able to verify certificate of any other node when using seed list URLs_. What are seed list URLs_? 
* Where is node-repository mapping saved? 

Here is my understanding from the original description.  Each DeGitX has a locator, which will find other nodes that has the same repository. The public and private keys are used to protect some information, such as the URLs of these nodes.   

#References

http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.68.4986&rep=rep1&type=pdf
