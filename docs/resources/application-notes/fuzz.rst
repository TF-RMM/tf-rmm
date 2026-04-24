.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

###########
RMM Fuzzing
###########

Configuration
=============

.. note::

   Only the LLVM-based toolchain (``afl-clang-lto`` and ``afl-clang-fast``) has been tested
   and is known to work.

This fuzzing setting uses `AFL++ <https://github.com/AFLplusplus/AFLplusplus>`.
AFL++ provides different modes, and we are using
`afl-clang-lto <https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.lto.md>`_ and the
`persistent mode <https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.persistent_mode.md>`_
for the best performance.

The source code is compiled with the compiler ``afl-clang-lto``, that (1)
'analyses' and 'instruments' the source code for better fuzzing result, better
coverage, for example, and (2) performs link-time optimization (LTO) on the
final executable.

By the time we are writing this readme, ``afl-clang-lto`` only exists in the
AFL++ for Linux.

The *persistent mode*, meanwhile, fuzzes the target (binary) multiple times in
a single fork, which accelerates the fuzzing process: we observe the speed-up is
around 3-5x for our setup to fuzz RMM.

Quick start
===========

Install AFL++
-------------

Download and install AFL++ as described in official `build documentation <https://github.com/AFLplusplus/AFLplusplus/blob/stable/docs/INSTALL.md>`.

.. code-block:: bash

   git clone https://github.com/AFLplusplus/AFLplusplus.git
   cd AFLplusplus
   make distrib
   sudo make install

It is recommended to use ramdisk as output directory to prevent SSD wear-out,
as AFL can carry out extensive I/O operations on the drive.
tmpfs can be used for that purpose in linux.

Use the commands below to create a 1GB ramdisk, and symlink it to ``_Fuzz/aflout/`` in project root.

.. code-block:: bash

   sudo mkdir -p /mnt/aflout
   sudo mount -t tmpfs -o size=1G tmpfs /mnt/aflout
   mkdir -p _Fuzz
   ln -s /mnt/aflout _Fuzz/aflout

Note that this directory will be wiped upon power reset.

Add this lines to ``/etc/fstab`` to create this directory on boot:

.. code-block:: text

   # Mount tmpfs for afl++ fuzzer output to avoid ssd wearout
   tmpfs   /mnt/aflout  tmpfs  defaults,size=1G  0  0

However, this will not prevent data loss on power reset, if you wish to preserve the fuzzing outputs, copy them before
the reset.

Install dependencies
--------------------

Install the required Python packages for corpus generation and coverage reporting:

.. code-block:: bash

   pip install -r tools/fuzz/python/requirements.txt

Install ``gnuplot`` for AFL plot generation:

.. code-block:: bash

   sudo apt install gnuplot

Build RMM with AFL++
--------------------
All commands below is meant to run from the project root.

**Source the env file for easy build:**

.. code-block:: bash

   source tools/fuzz/fuzz.env

Note that the command on the env file, depends on the ``/mnt/aflout`` directory that was created in the previous step.

**Build:**

.. code-block:: bash

   fuzzbuild 1 buildName

Replace buildName with desired name for your fuzzing build.
This will create ``_Fuzz/buildName`` directory
If you don't need coverage info, then replace 1 with 0.

For non-persistent mode append ``np`` to the command:

.. code-block:: bash

   fuzzbuild 1 buildName2 np

Compiling in none persistent mode will let you run rmm with desired corpus as input.
After the build, script will present possible commands that you might want to run, such as:

.. code-block:: bash

   ./_Fuzz/builds/buildName2/Debug/rmm.elf _Fuzz/buildName2/smc_corpus/default.bin

**Fuzz:**

Run fuzzer for ~15 minutes (1000 seconds):

.. code-block:: bash

   cmake --build _Fuzz/builds/buildName -- run-fuzzer

For quick benchmarking after making changes in code you may run:

.. code-block:: bash

   cmake --build _Fuzz/builds/buildName -- quick-bench

This will create afl plot and coverage info automatically.

Check cmake file ``tools/fuzz/CMakeLists.txt`` to inspect and tune fuzzing commands.

**Parallel Fuzzing**

To make use of multiple cores for fuzzing consider using multiple fuzzing instances.
Multiple fuzzers can be spawned with multirun.py script.

.. code-block:: bash

   python tools/fuzz/python/multirun.py spawn -b buildName -w 4  -V 100 --no-ui --mix

Number of workers, fuzzing duration and other options can be adjusted.
To see available options, run the script with --help flag.

More
====

Generate corpus
---------------

AFL++ needs some initial inputs, or corpus.
Ideally, we should provide some meaningful corpus as the 'seed' for fuzzing.
Read more about generating corpora and existing corpora in :doc:`corpora`.
