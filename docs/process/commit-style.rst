.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Commit Style
============

When writing commit messages, please think carefully about the purpose and scope
of the change you are making: describe briefly what the change does, and
describe in detail why it does it. This helps to ensure that changes to the
code-base are transparent and approachable to reviewers, and it allows us to
keep a more accurate changelog. You may use Markdown in commit messages.

A good commit message provides all the background information needed for
reviewers to understand the intent and rationale of the patch. This information
is also useful for future reference. For example:

- What does the patch do?
- What motivated it?
- What impact does it have?
- How was it tested?
- Have alternatives been considered? Why did you choose this approach over
  another one?
- If it fixes an `issue`_, include a reference.

    - Github prescribes a format for issue fixes that can be used within the
      commit message:

      .. code::

          Fixes TF-RMM/tf-rmm#<issue-number>

Commit messages are expected to be of the following form, based on conventional
commits:

.. code::

    <type>[optional scope]: <description>

    [optional body]

    [optional trailer(s)]

The following `types` are permissible :

+--------------+---------------------------------------------------------------+
| Type         | Description                                                   |
+==============+===============================================================+
| ``feat``     | A new feature                                                 |
+--------------+---------------------------------------------------------------+
| ``fix``      | A bug fix                                                     |
+--------------+---------------------------------------------------------------+
| ``build``    | Changes that affect the build system or external dependencies |
+--------------+---------------------------------------------------------------+
| ``docs``     | Documentation-only changes                                    |
+--------------+---------------------------------------------------------------+
| ``perf``     | A code change that improves performance                       |
+--------------+---------------------------------------------------------------+
| ``refactor`` | A code change that neither fixes a bug nor adds a feature     |
+--------------+---------------------------------------------------------------+
| ``revert``   | Changes that revert a previous change                         |
+--------------+---------------------------------------------------------------+
| ``style``    | Changes that do not affect the meaning of the code            |
|              | (white-space, formatting, missing semi-colons, etc.)          |
+--------------+---------------------------------------------------------------+
| ``test``     | Adding missing tests or correcting existing tests             |
+--------------+---------------------------------------------------------------+
| ``chore``    | Any other change                                              |
+--------------+---------------------------------------------------------------+

The permissible `scopes` are more flexible, and we recommend that they match
the directory where the patch applies (or where the main subject of the
patch is, in case of changes accross several directories).

The following example commit message demonstrates the use of the
``refactor`` type and the ``lib/arch`` scope:

.. code::

    refactor(lib/arch): ...

    This change introduces ....

    Change-Id: ...
    Signed-off-by: ...

In addition, the width of the commit message must be no more than 72 characters.

.. _mandated-trailers:

Mandated Trailers
-----------------

Commits are expected to be signed off with the ``Signed-off-by:`` trailer using
your real name and email address. You can do this automatically by committing
with Git's ``-s`` flag.

There may be multiple ``Signed-off-by:`` lines depending on the history of the
patch. See :ref:`copyright-license-guidance` for guidance on this.

Ensure that each commit also has a unique ``Change-Id:`` line. If you have
cloned the repository using the "`Clone with commit-msg hook`" clone method,
then this should be done automatically for you.

More details may be found in the `Gerrit Change-Ids documentation`_.

--------------

.. _Gerrit Change-Ids documentation: https://review.trustedfirmware.org/Documentation/user-changeid.html
.. _issue: https://github.com/TF-RMM/tf-rmm/issues
