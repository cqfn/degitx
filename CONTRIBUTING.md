# Contributing guide

You can contribute in different ways to the project: reporting bugs, solving tasks, reviewing pull requests.

## Bug reporting

Make sure the title of the issue explains the problem you are having.
Also, the description of the issue must clearly explain what is broken,
not what you want us to implement.
Go through this checklist and make sure you answer "YES" to all points:
 - You have all pre-requisites listed in README.md installed
 - You are sure that you are not reporting a duplicate (search all issues)
 - You say "is broken" or "doesn't work" in the title
 - You tell us what you are trying to do
 - You explain the results you are getting
 - You suggest an alternative result you would like to see

This article will help you understand what we are looking for:
http://www.yegor256.com/2014/11/24/principles-of-bug-tracking.html

## Task solving

If you want to solve a task, please ask project architect to assing you a ticket first,
and get the approve. The ticket can be approved by different ways:
 - Ticket has `scope` label
 - Ticket has milestone attached

Different people can be involved in task solving workflow, sometimes one people may have different roles:
 - "Author" - the person who reported the ticket
 - "Performer" - the person who is solving the ticket
 - "Reviewer" - the person who reviews proposed solution
 - "Architect" - the person who is merging changes to `master`

The workflow is:
 1. Author reports a ticket
 2. Architect adds ticket to scope and assigns the ticket to performer
 3. Performer proposes a solution to solve the problem (one or more pull requests)
 4. Reviewer reviews each pull requests, and approves it finally (optional if architect reviews PR)
 5. Architect reviews each pull request, and merges it finally
 6. Performer asks author to close the ticket (sometimes it's OK to close ticket via PR "linked issues" feature)
 7. Author closes the ticket, it can be counted as done (until closed, the task has "in progress" status)

The proposed solution for task should be presented as a pull request from
some branch to `master` branch of repository. Please start branch name
with ticket number, e.g. `66-contributing` branch for `#66` ticket.
Start new branch from fresh `master` branch to avoid conflicts.
Commit changes, use this format for commit messages:
```
#<ticket-number> - short summary

optional description
```
It's recommended to sign your commits with GPG key, but not mandatory yet.

When submitting a pull request, make sure that you can say "YES" to each point in this short checklist:
 - You what problem is solving by PR in the title
 - You explain the proposed solution in PR description, and start it with solving ticket reference
 - You made a small amount of changes (can be reviewed by a stranger in 15 minutes)
 - You made changes related to only one bug (create separate PRs for separate problems)
 - You are ready to defend your changes (there will be a code review)
 - You don't touch what you don't understand
 - You ran the build locally and it passed

Please try to avoid using "closing" GitHub keywords or "linked issues" with one exception:
it OK to close a ticket by PR only if ticket's "author" is project's "architect"
and PR **fully** solves a problem from the ticket (there are no next steps related to this ticket).

This article will help you understand what we are looking for:
http://www.yegor256.com/2015/02/09/serious-code-reviewer.html
