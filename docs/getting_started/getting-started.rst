.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

.. _getting_started:

#############
Prerequisite
#############

This document describes the software requirements for building |RMM| for
AArch64 target platforms.

It may possible to build |RMM| with combinations of software packages that
are different from those listed below, however only the software described in
this document can be officially supported.

###########
Build Host
###########

The |RMM| officially supports a limited set of build environments and setups.
In this context, official support means that the environments listed below
are actively used by team members and active developers, hence users should
be able to recreate the same configurations by following the instructions
described below. In case of problems, the |RMM| team provides support only
for these environments, but building in other environments can still be
possible.

We recommend at least Ubuntu 20.04 LTS (x64) for build environment. The
arm64/AArch64 Ubuntu and other Linux distributions should also work fine,
provided that the necessary tools and libraries can be installed.

.. _tool_dependencies:

##########################
Tool & Dependency overview
##########################

The following tools are required to obtain and build |RMM|:

.. csv-table:: Tool dependencies
   :header: "Name", "Version", "Component"

   "C compiler", see :ref:`getting_started_toolchain` ,"Firmware"
   "CMake", ">=3.15.0", "Firmware, Documentation"
   "GNU Make", ">4.0", "Firmware, Documentation"
   "Python",3.x,"Firmware, Documentation"
   "Perl",>=5.26,"Firmware, Documentation"
   "ninja-build",,"Firmware (using Ninja Generator)"
   "Sphinx",">=2.4,<3.0.0","Documentation"
   "sphinxcontrib-plantuml",,"Documentation"
   "sphinx-rtd-theme",,"Documentation"
   "Git",, "Firmware, Documentation"
   "Graphviz dot",">v2.38.0","Documentation"
   "docutils",">v2.38.0","Documentation"
   "gcovr",">=v4.2","Tools(Coverage analysis)"
   "CBMC",">=5.84.0","Tools(CBMC analysis)"
   "Cppcheck",">=2.14.0","Tools(Cppcheck)"

.. _getting_started_toolchain:

###############
Setup Toolchain
###############

To compile |RMM| code for an AArch64 target, at least one of the
supported AArch64 toolchains have to be available in the
build environment.

Currently, the following compilers are supported:

- GCC (aarch64-none-elf-) >= 10.2-2020.11 (from the `Arm Developer website`_)
- Clang+LLVM >= 14.0.0 (from the `LLVM Releases website`_)

The respective compiler binary must be found in the shell's search path.
Be sure to add the bin/ directory if you have downloaded a binary version.
The toolchain to use can be set using ``RMM_TOOLCHAIN`` parameter and can
be set to either `llvm` or `gnu`. The default toolchain is `gnu`.

For non-native AArch64 target build, the ``CROSS_COMPILE`` environment
variable must contain the right target triplet corresponding to the AArch64
GCC compiler. Below is an example when RMM is to be built for AArch64 target
on a non-native host machine and using GCC as the toolchain.

    .. code-block:: bash

      export CROSS_COMPILE=aarch64-none-elf-
      export PATH=<path-to-aarch64-gcc>/bin:$PATH

Please note that AArch64 GCC must be included in the shell's search path
even when using Clang as the compiler as LLVM does not include some C
standard headers like `stdlib.h` and needs to be picked up from the
`include` folder of the AArch64 GCC. Below is an example when RMM is
to be built for AArch64 target on a non-native host machine and using
LLVM as the toolchain.

    .. code-block:: bash

      export CROSS_COMPILE=aarch64-none-elf-
      export PATH=<path-to-aarch64-gcc>/bin:<path-to-clang+llvm>/bin:$PATH

The ``CROSS_COMPILE`` variable is ignored for ``fake_host`` build and
the native host toolchain is used for the build.

#######################################
Package Installation (Ubuntu-20.04 x64)
#######################################

If you are using the recommended Ubuntu distribution then we can install the
required packages with the following commands:

1. Install dependencies:

.. code:: shell

    sudo apt-get install -y git build-essential python3 python3-pip make ninja-build
    sudo snap install cmake

2. Verify cmake version:

.. code-block:: bash

    cmake --version

.. note::

    Please download cmake 3.19 or later version from https://cmake.org/download/.

3. Add CMake path into environment:

.. code-block:: bash

    export PATH=<CMake path>/bin:$PATH

###########################
Install python dependencies
###########################

.. note::

    The installation of Python dependencies is an optional step. This is required only
    if building documentation.

RMM's ``docs/requirements.txt`` file declares additional Python dependencies.
Install them with ``pip3``:

.. code-block:: bash

    pip3 install --upgrade pip
    cd <rmm source folder>
    pip3 install -r docs/requirements.txt

############################################
Install coverage tools analysis dependencies
############################################

.. note::

    This is an optional step only needed if you intend to run coverage
    analysis on the source code.

On Ubuntu, ``gcovr`` tool can be installed in two different ways:

Using the package manager:

.. code-block:: bash

    sudo apt-get install gcovr

The second (and recommended) way is install it with ``pip3``:

.. code-block:: bash

    pip3 install --upgrade pip
    pip3 install gcovr

.. _getting_started_get_source:

#########################
Getting the RMM Source
#########################

Source code for |RMM| is maintained in a Git repository hosted on TrustedFirmware.org.
To clone this repository from the server, run the following in your shell:

.. code-block:: bash

    git clone --recursive https://git.trustedfirmware.org/TF-RMM/tf-rmm.git

Additional steps for Contributors
*********************************

If you are planning on contributing back to RMM, your commits need to
include a ``Change-Id`` footer as explained in :ref:`mandated-trailers`.
This footer is generated by a Git hook that needs to be installed
inside your cloned RMM source folder.

The `TF-RMM Gerrit page`_ under trustedfirmware.org contains a
*Clone with commit-msg hook* subsection under its **Download** header where
you can copy the command to clone the repo with the required git hooks. Please
use the **SSH** option to clone the repository on your local machine.

If needed, you can also manually install the hooks separately on an existing
repo:

.. code:: shell

    curl -Lo $(git rev-parse --git-dir)/hooks/commit-msg https://review.trustedfirmware.org/tools/hooks/commit-msg
    chmod +x $(git rev-parse --git-dir)/hooks/commit-msg

You can read more about Git hooks in the *githooks* page of the `Git hooks
documentation`_.

General contribution guidelines for contributors can be found in
:ref:`Contributor's Guide`.

#################################
Install Cppcheck and dependencies
#################################

.. note::

    The installation of Cppcheck is an optional step. This is required only
    if using the Cppcheck static analysis.

The recommended version of Cppcheck is indicated in :ref:`tool_dependencies`.
See :ref:`Cppcheck Application Note` for installation steps and details
on how to use it within RMM build system.

############
Install CBMC
############

.. note::

    The installation of CBMC is an optional step. This is required only
    if running source code analysis with CBMC.

Follow the public documentation to install CBMC either from the official
website https://www.cprover.org/cbmc/ or from the official github
https://github.com/diffblue/cbmc

Refer to :ref:`CBMC` Application Notes for details on installation and
running CBMC analysis on TF-RMM sources.

##################
Install Clang-tidy
##################

Clang-tidy is included in LLVM release package. It can also be installed via
package manager :

.. code-block:: bash

    sudo apt-get install clang-tidy

Note that the ``RMM_TOOLCHAIN`` needs to be set to `llvm` to run clang-tidy
build targets from RMM build system.

###########################
Performing an Initial Build
###########################

The |RMM| sources can be compiled using multiple CMake options.

For detailed instructions on build configurations and examples
see :ref:`build_options_examples`.

A typical build command for the FVP platform using GCC toolchain
is shown below:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR}

###############
Running the RMM
###############

The |RMM| is part of the CCA software stack and relies on EL3 Firmware to load
the binary at boot time appropriately. It needs both EL3 Firmware and
Non-Secure Host to be present at runtime for its functionality. The EL3
Firmware must comply to `RMM-EL3 Communication Specification`_ and is
typically the `TF-A`_. The Non-Secure Host can be an RME aware hypervisor
or an appropriate Test utility running in Non-Secure world which can interact
with |RMM| via Realm Management Interface (RMI).

Building all of the involved stack is complicated. We recommend using the
`Shrinkwrap`_ tooling to bootstrap the stack. For more details on `Shrinkwrap`_
and utilizing configs and overlays included in |RMM| please refer to
:ref:`using_shrinkwrap_with_rmm` and, specially for building a demonstrator
for 3-world, you can refer to :ref:`3_world_testing`.

The |TF-A| documentation also provides some documentation to build |TF-A| and
other pieces of firmware for RME in `TF-A RME documentation`_. The |RMM| build
option in |TF-A| should point to the ``rmm.img`` binary generated by building
|RMM|.

If |RMM| is built for the `fake_host` architecture
(see :ref:`RMM Fake Host Build`), then the generated `rmm.elf` binary can
run natively on the Host machine. It does this by emulating parts of the system
as described in :ref:`RMM Fake host architecture` design.

-----

.. _Arm Developer website: https://developer.arm.com/open-source/gnu-toolchain/gnu-a/downloads
.. _LLVM Releases website: https://releases.llvm.org/
.. _RMM-EL3 Communication Specification: https://trustedfirmware-a.readthedocs.io/en/latest/components/rmm-el3-comms-spec.html
.. _TF-A: https://www.trustedfirmware.org/projects/tf-a/
.. _TF-A RME documentation: https://trustedfirmware-a.readthedocs.io/en/latest/components/realm-management-extension.html
.. _TF-RMM Gerrit page: https://review.trustedfirmware.org/admin/repos/TF-RMM/tf-rmm
.. _Git hooks documentation:  https://git-scm.com/docs/githooks
.. _Shrinkwrap: https://shrinkwrap.docs.arm.com
