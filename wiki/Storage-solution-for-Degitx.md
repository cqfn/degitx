If we decide to go with Kubernetes to manage all the backend nodes, we will have to evaluate some open source storage solutions.  Here is a good web site to compare available solutions. https://medium.com/volterra-io/kubernetes-storage-performance-comparison-v2-2020-updated-1c0b69f0dcf4

There are some suggestions that we can adopt the services from the public Cloud Providers. For instance, if the system decides to use a database to keep all the metadata information for the nodes, we could use MongoDB. We can also consider the storage that supports the strong consistency on write.  