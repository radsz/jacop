# Git Workflow JaCoP

First, please read carefully all different git workflows explained in the tutorial prepared by Atlassian. This tutorial
is available from the link

https://www.atlassian.com/git/workflows

This tutorial gently introduces the concepts and manner we are working with Git. The core developers of JaCoP follow
closely the gitflow workflow model. The contributions from open source community are likely to come in the form as
explained in a forking workflow. Therefore, feel free to fork our work and contribute back by issuing the pull request.
However, to increase the likelihood of the pull please discuss with us first to make sure that you understand our goals
concerning JaCoP. We are quite opinionated and strive to deliver a great quality product. We will hold you to the same
standards as we want to hold ourselves.

The gitflow workflow is explained in more details in the following links that are also recommended reading as it will
help you to become more productive thanks to git.

http://nvie.com/posts/a-successful-git-branching-model/
Check Getting Started in https://github.com/nvie/gitflow

Good tirade against having no work flow git model.
https://sandofsky.com/blog/git-workflow.html

Very nice presentation about git workflows is available at youtube (the link starts video at the right moment).
http://youtu.be/GYnOwPl8yCE?t=53m13s

As said in the youtube video above - Branches are your lego blocks. Use them to organize your work and make it fit your
working style.

We are using SourceTree from Atlassian to make it easier to follow gitflow workflow. It can be downloaded from
https://www.atlassian.com/software/sourcetree/overview

Git is an awesome tool and we are continuously learning it. We may, by mistake, not always follow this workflow.
We may evolve this workflow later on and it will be reflected in this document. Feel free to send us your comments
(pull request on this document ;) ) if you think we can improve our way of using git.

# Summary of Git Workflow

1. We care about commit history and do our best to keep it clean and easier to investigate later on.

2. **master** branch - Primary branch to store **Production-Ready** code. It is what we are ready to support and help you
   with if you find bugs in it.

3. **develop** branch - Primary branch to store **Latest-Development** state for the next release on the master branch.
    It is a branch that is checked by continuous integration server (Jenkins).

4. **feature/ ** branches - Secondary branch to store **Particular Feature** fine-grained work-in-progress. It always branches
   off latest Develop branch. It merges back into Develop then it is discarded. You merge it back when you are done
   (as defined by core developer team) and the branch is discarded. The feature branch may be discarded without merging
   if it was a failed experiment that did not work out. The feature branches can be short and long running.

5. **release/ ** branches - Secondary branch to store **Release Candidate** in this branch only preparatory work for the
    release happens. It sits between **develop** and **master**. It branches from **develop**. It merges back into both
    **master** and **develop**. It is discarded after merging.

6. **hotfix/ ** branches - Secondary branch to quickly resolve emergency problems with existing supported production release.
   It is branched from **master**. After fix is concluded it is merged back into both **master** and **develop**. It is discarded
   after merging. This branch should contain a test that exhibits a reported bug that caused a need for bug fix.

7. We have no support branches as we are only supporting the latest version available on **master** branch and support for
   this one is taken care of by **hotfix** branches.

8. **radek/ ** and **kris/ ** branches - personal branches of core developers that can contain anything in any manner the
    author wishes so, but if the history is not proper all the commits may be squashed into one and rebased onto a
    feature branch before it is merged into **develop** branch. Those personal branches are never merged into other branches.





