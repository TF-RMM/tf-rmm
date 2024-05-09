.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

*******************
Contributor's Guide
*******************

Getting Started
===============

-  Make sure you have a Github account and you are logged on
   `review.trustedfirmware.org`_.

-  Clone `RMM`_ on your own machine as described in
   :ref:`getting_started_get_source`.

-  If you plan to contribute a major piece of work, it is usually a good idea to
   start a discussion around it on the mailing list. This gives everyone
   visibility of what is coming up, you might learn that somebody else is
   already working on something similar or the community might be able to
   provide some early input to help shaping the design of the feature.

-  If you intend to include Third Party IP in your contribution, please mention
   it explicitly in the email thread and ensure that the changes that include
   Third Party IP are made in a separate patch (or patch series).

-  Create a local topic branch based on the `RMM`_ ``main`` branch.

Making Changes
==============

-  See the `License and Copyright for Contributions`_ section for guidance
   on license and copyright.

-  Ensure commits adhere to the project's :ref:`Commit Style`.

-  Make commits of logical units. See these general `Git guidelines`_ for
   contributing to a project.

-  Keep the commits on topic. If you need to fix another bug or make another
   enhancement, please address it on a separate topic branch.

-  Split the patch into manageable units. Small patches are usually easier to
   review so this will speed up the review process.

-  Avoid long commit series. If you do have a long series, consider whether
   some commits should be squashed together or addressed in a separate topic.

-  Follow the :ref:`Coding Standard`.

-  Use the static checks as shown in :ref:`build_options_examples` to perform
   checks like checkpatch, checkspdx, header files include order, clang-tidy,
   cppcheck etc. A sample static analysis command line is given below, assuming
   the tools have been setup as per instruction in :ref:`getting_started`.

   .. code-block:: bash

      cd $rmm_root
      cmake -DRMM_CONFIG=fvp_defcfg -S . -B build -DRMM_TOOLCHAIN=llvm -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
      cmake --build build -- checkpatch checkspdx-patch checkincludes-patch clang-tidy-patch cppcheck-misra

-  Where appropriate, please update the documentation.

   -  Consider whether the :ref:`Design` document or other in-source
      documentation needs updating.

-  Ensure that each patch in the patch series compiles in all supported
   configurations. For generic changes, such as on the libraries, The
   :ref:`RMM Fake host architecture` should be able to, at least,
   build. Patches which do not compile will not be merged.

-  Please test your changes and add suitable tests in the available test
   frameworks for any new functionality.

Submitting Changes
==================

-  Assuming the clone of the repo has been done as mentioned in the
   :ref:`getting_started_get_source` and *origin* refers to the upstream repo,
   submit your changes for review targeting the ``integration`` branch.
   Create a topic that describes the target of your changes to help group
   related patches together.

   .. code::

       git push origin HEAD:refs/for/integration [-o topic=<your_topic>]

   Refer to the `Gerrit Uploading Changes documentation`_ for more details.

-  Add reviewers for your patch:

   -  At least one maintainer. See the list of :ref:`maintainers`.

   -  Alternatively, you might send an email to the `TF-RMM mailing list`_
      to broadcast your review request to the community.

-  The changes will then undergo further review by the designated people. Any
   review comments will be made directly on your patch. This may require you to
   do some rework. For controversial changes, the discussion might be moved to
   the `TF-RMM mailing list`_ to involve more of the community.

-  The patch submission rules are the following. For a patch to be approved
   and merged in the tree, it must get a ``Code-Review+2``.

   In addition to that, the patch must also get a ``Verified+1``. This is
   usually set by the Continuous Integration (CI) bot when all automated tests
   passed on the patch. Sometimes, some of these automated tests may fail for
   reasons unrelated to the patch. In this case, the maintainers might
   (after analysis of the failures) override the CI bot score to certify that
   the patch has been correctly tested.

   In the event where the CI system lacks proper tests for a patch, the patch
   author or a reviewer might agree to perform additional manual tests
   in their review and the reviewer incorporates the review of the additional
   testing in the ``Code-Review+1`` to attest that the patch works as expected.

-  When the changes are accepted, the :ref:`maintainers` will integrate them.

   -  Typically, the :ref:`maintainers` will merge the changes into the
      ``integration`` branch.

   -  If the changes are not based on a sufficiently-recent commit, or if they
      cannot be automatically rebased, then the :ref:`maintainers` may rebase it
      on the ``integration`` branch or ask you to do so.

   -  After final integration testing, the changes will make their way into the
      ``main`` branch. If a problem is found during integration, the
      :ref:`maintainers` will request your help to solve the issue. They may
      revert your patches and ask you to resubmit a reworked version of them or
      they may ask you to provide a fix-up patch.

.. _copyright-license-guidance:

License and Copyright for Contributions
=======================================

All new files should include the BSD-3-Clause SPDX license identifier
where possible. When contributing code to us, the committer and all authors
are required to make the submission under the terms of the
:ref:`Developer Certificate of Origin`, confirming that the code submitted can
(legally) become part of the project, and be subject to the same BSD-3-Clause
license. This is done by including the standard Git ``Signed-off-by:``
line in every commit message. If more than one person contributed to the
commit, they should also add their own ``Signed-off-by:`` line.

Files that entirely consist of contributions to this project should
have a copyright notice and BSD-3-Clause SPDX license identifier of
the form :

.. code::

   SPDX-License-Identifier: BSD-3-Clause
   SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Patches that contain changes to imported Third Party IP files should retain
their original copyright and license notices. If changes are made to the
imported files, then add an additional ``SPDX-FileCopyrightText`` tag line
as shown above.

--------------

.. _review.trustedfirmware.org: https://review.trustedfirmware.org
.. _RMM: https://git.trustedfirmware.org/TF-RMM/tf-rmm.git
.. _Git guidelines: http://git-scm.com/book/ch5-2.html
.. _Gerrit Uploading Changes documentation: https://review.trustedfirmware.org/Documentation/user-upload.html
.. _TF-A Tests: https://trustedfirmware-a-tests.readthedocs.io
.. _TF-RMM mailing list: https://lists.trustedfirmware.org/mailman3/lists/tf-rmm.lists.trustedfirmware.org/
