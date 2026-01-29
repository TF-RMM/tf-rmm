.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

.. _using_shrinkwrap_with_rmm:

Building with Shrinkwrap
************************

This document explains how to build and run |RMM| in |FVP|, including all
necessary firmware images, by using `Shrinkwrap`_.

Introduction
____________

`Shrinkwrap`_ is a tool that helps to simplify the process of building and
running firmware on Arm |FVP| by providing an intuitive command line interface
frontend and (by default) a container-based backend.

Shrinkwrap works by using *configs*, which are defined in YAML and can be easily
extended using a built-in layering system.

For instructions on how to setup Shrinkwrap on your local machine as well as for
further information, you can refer to the `Quick Start Guide`_. In particular,
for development with RME enabled Linux in Normal World, please refer to the
`3 world configuration`_. In case that the Secure World also needs to be
included, please refer to the `4 world configuration`_

.. _Setup_local_RMM_with_Shrinkwrap:

Setup local RMM with Shrinkwrap
_______________________________

This section assumes that you have your local |RMM| repository cloned
and that it is used for your development. In order to help using
Shrinkwrap with your development workflow, the project provides some
configs and overlays.

Also, from now on, it is assumed that your current directory (pointed by
``${PWD}``) is the root of your |RMM| development repository.

In order to use the configs defined in |RMM|, it is essential to configure
the ``${SHRINKWRAP_CONFIG}`` environment variable to point to
``${PWD}/tools/shrinkwrap/configs`` directory so the tool can locate the
config yaml files.

    .. code-block:: shell

      export SHRINKWRAP_CONFIG=${PWD}/tools/shrinkwrap/configs

It is also recommended to override the default ``${SHRINKWRAP_BUILD}`` and
``${SHRINKWRAP_PACKAGE}`` environment variables to a known workspace directory,
as shown below:

    .. code-block:: shell

      export WORKSPACE=${HOME}/workspace
      export SHRINKWRAP_BUILD=${WORKSPACE}
      export SHRINKWRAP_PACKAGE=${SHRINKWRAP_BUILD}/package

When building, Shrinkwrap will store the sources inside
``${SHRINKWRAP_BUILD}/source/<CONFIG_NAME>`` and the build artifacts and
packages will be stored inside ``${SHRINKWRAP_BUILD}/build/<CONFIG_NAME>`` and
``${SHRINKWRAP_PACKAGE}/<CONFIG_NAME>`` directories respectively.

.. note::

      By default, if ${SHRINKWRAP_BUILD} and ${SHRINKWRAP_PACKAGE} are not
      specified, Shrinkwrap will use the ``${HOME}/.shrinkwrap`` as default
      value for ${SHRINKWRAP_BUILD}. It is only necessary to overwrite the
      environment variables in the case it is needed to build in a different
      location.

.. _3_world_testing:

3-World testing
_______________

|RMM| provides a number of overlays that can be used in conjunction with some
of the configs provided by Shrinkwrap. One of the overlays, specifically
``rmm.yaml``, can be used along with the ``cca-3world.yaml`` to
build a 3 World demonstrator using the ``master`` branch of |TF-A| and the
local |RMM| repository.

As an example, the following command line would build the 3-World demonstrator.
It assumes that Shrinkwrap is called from within the ``<RMM_ROOT>`` directory:

    .. code-block:: shell

       shrinkwrap build cca-3world.yaml --overlay=buildroot.yaml --overlay=rmm.yaml --btvar=GUEST_ROOTFS='${artifact:BUILDROOT}' --btvar=RMM_SRC=${PWD} --no-sync=rmm

You can find further instructions on how to build and package the filesystem
and required binaries in the `3 world configuration`_ documentation.

To run the demonstrator, use the following command:

    .. code-block:: shell

       shrinkwrap run cca-3world.yaml --rtvar=ROOTFS=${SHRINKWRAP_PACKAGE}/cca-3world/rootfs.ext2

3-World testing with CCA DA
___________________________

Follow the instructions in :ref:`Setup_local_RMM_with_Shrinkwrap` to setup the
local RMM with shrinkwrap.

RMM provides ``cca_da.yaml`` overlay that can be used along with the
``cca-3world.yaml`` to build a 3 World demonstrator.

As an example, the following command line would build the 3-World demonstrator.
It assumes that Shrinkwrap is called from within the ``<RMM_ROOT>`` directory
that was created in the last step:

    .. code-block:: shell

       shrinkwrap build cca-3world.yaml --overlay=cca_da.yaml --btvar GUEST_ROOTFS='${artifact:BUILDROOT}' --btvar RMM_SRC=${PWD} --no-sync=rmm

Follow the steps mentioned in  `3 world configuration`_ documentation to copy
guest-disk.img, Image, KVMTOOL_EFI.fd and lkvm to the host filesystem.

Now you can boot the host, using the rootfs we just modified.

    .. code-block:: shell

       shrinkwrap run cca-3world.yaml --overlay=cca_da.yaml --rtvar ROOTFS=${SHRINKWRAP_PACKAGE}/cca-3world/rootfs.ext2


Finally, once the host has booted, log in as "root" (no password). Below are the
device assignment workflow based on the `DA workflow`_ cover letter from the
Linux kernel prototype branch.

Connect the device with TSM, this establishes secure session to the device and
enables IDE in the link.

    .. code-block:: shell

       echo 0000:02:00.0 > /sys/bus/pci/devices/0000:02:00.0/driver/unbind
       echo vfio-pci > /sys/bus/pci/devices/0000:02:00.0/driver_override
       echo 0000:02:00.0 > /sys/bus/pci/drivers_probe
       echo tsm0 > /sys/bus/pci/devices/0000:02:00.0/tsm/connect

Now, launch a realm using kvmtool from the /cca directory (that was created
above):

    .. code-block:: shell

       cd /cca
       ./lkvm run --realm -c 2 -m 256 --disk guest-disk.img --kernel Image -p "earlycon=uart,mmio,0x101000000 root=/dev/vda2" --iommufd-vdevice --vfio-pci 0000:02:00.0


Be patient while this boots to the shell.

Now in the Realm we follow the below steps on the assigned device to move the
device to TDISP LOCKED and RUN state. At this step the Realm verifies the
device attestation evidence that it got from the Host are valid by computing the
digest and comparing it with the value it got from the RMM.

    .. code-block:: shell

       echo 0000:00:00.0 > /sys/bus/pci/devices/0000:00:00.0/driver/unbind
       echo tsm0 > /sys/bus/pci/devices/0000:00:00.0/tsm/lock
       echo 1 > /sys/bus/pci/devices/0000:00:00.0/tsm/accept

Load the driver

    .. code-block:: shell

       echo 0000:00:00.0 > /sys/bus/pci/drivers_probe


If everything went well, you should see the driver loading and the following
lines in the console:

    .. code-block:: console

        ata1: SATA max UDMA/133 abar m8192@0x50006000 port 0x50006100 irq 22 lpm-pol 1
        ata1: SATA link up 6.0 Gbps (SStatus 133 SControl 300)
        ata1.00: ATA-10: ahci-disk.img, 0.1.0, max MWDMA2
        ata1.00: 131072 sectors, multi 0: LBA48 NCQ (depth 1)
        ata1.00: configured for PIO4
        scsi 0:0:0:0: Direct-Access     ATA      ahci-disk.img    0    PQ: 0 ANSI: 5
        sd 0:0:0:0: [sda] 131072 512-byte logical blocks: (67.1 MB/64.0 MiB)
        sd 0:0:0:0: [sda] Write Protect is off
        sd 0:0:0:0: [sda] Write cache: disabled, read cache: enabled, doesn't support DPO or FUA
        sd 0:0:0:0: [sda] Preferred minimum I/O size 512 bytes
        sd 0:0:0:0: [sda] Attached SCSI disk


Also the device should be visible as a device in `/dev` , in this case /dev/sda will be
visible. You can now partition, format and mount the device as you would do with any other
block device.


Testing RMM with TFTF
_____________________

|RMM| provides a config that brings together a software stack to test |RMM|
and Arm RME extension utilizing `TF-A-Tests`_. The main Test payload in
TF-A-Tests is the |TFTF| binary. In this config, |TF-A| is in Root World, |RMM|
is in Realm EL2 and |TFTF| is in Normal World.

In order to build the config, you need to run the following command:

    .. code-block:: shell

      shrinkwrap build --btvar=RMM_SRC=${PWD} rmm-tftf.yaml --no-sync=rmm

and you can run it through

    .. code-block:: shell

      shrinkwrap run rmm-tftf.yaml

For further documentation about this configuration, you can check the docs through

    .. code-block:: shell

      shrinkwrap inspect rmm-tftf.yaml

The build and run commands can also be found in the documentation of the config
yaml file. When invoking the ``build`` command, Shrinkwrap will store the
external repositories inside the ``${SHRINKWRAP_BUILD}/sources/<CONFIG_NAME>``
directory.

Overlays
________

Overlays can be used to extend the functionality of a config by overwriting
both build and runtime settings. They can be used on any configuration and they
can be combined in any way needed.

In order to use an overlay, they need to be specified on the command line, through
the ``--overlay`` keyword, as follows:

    .. code-block:: shell

      shrinkwrap build rmm-tftf.yaml --btvar=RMM_SRC=${PWD} --overlay=<OVERLAY_FILE_NAME> --no-sync=rmm
      shrinkwrap run rmm-tftf.yaml --overlay=<OVERLAY_FILE_NAME>

The path to the overlay can be relative to where Shrinkwrap is called from and you
can use as many ``--overlay`` statements as needed.

Overlays are stored in the ``<RMM_ROOT_DIR>/tools/shrinkwrap/configs/`` directory,
alongside with the configuration files.

The available Overlays are sumarized in the next table

.. csv-table::
   :header: "Overlay", "Description"
   :widths: 2 8

   lfa-support.yaml,Overlay to build |TF-A| with LFA support enabled and load LFA RMM at expected address.
   model-enable-lpa2.yaml,Overlay used to enable ``FEAT_LPA2`` on the |FVP| model at run time. In addition this overlay also sets the ``PA_SIZE`` on the model to 52
   model-enable-mec.yaml,Overlay used to enable ``FEAT_MEC`` on the |FVP| model at run time.
   model-wait-debugger.yaml,Overlay to configure the |FVP| model to listen for Iris connections on port 7100 and make it wait until a debugger is connected before starting execution
   model-enable-s2pie-s2poe.yaml,Overlay to enable ``FEAT_S2PIE`` and ``FEAT_S2POE`` on the |FVP| model at run time.
   model-enable-feat_d128.yaml,Overlay used to enable ``FEAT_D128`` on the |FVP| model at runtime.
   rmm-debug.yaml,Overlay to build |RMM| (as well as |TF-A|) in debug mode
   rmm-v1_1.yaml,Overlay to build |RMM| with v1.1 features
   clean.yaml,Overlay used to avoid an exception with ``Shrinkwrap clean`` in which a path with a valid format needs to be specified for |RMM|

Example of use
~~~~~~~~~~~~~~

Below is an example on how to use one of the available overlays with the
existing configuration. The example specifies ``--runtime=null`` to use the
native toolchain (without the Docker container) to build the artifacts and
``--no-sync-all`` to prevent Shrinkwrap from updating/cleaning any of the
repositories:

    .. code-block:: shell

       shrinkwrap --runtime=null build rmm-tftf.yaml --overlay=model-enable-lpa2.yaml --btvar=RMM_SRC=${PWD} --no-sync-all

Similarly you can use overlay rmm-v1_1.yaml to enable RMM v1.1 features along
with rmm-debug.yaml to enable debug build.

    .. code-block:: shell

       shrinkwrap --runtime=null build rmm-tftf.yaml --overlay=rmm-v1_1.yaml --overlay=rmm-debug.yaml --btvar=RMM_SRC=${PWD} --no-sync-all

Then you run your tests with

    .. code-block:: shell

       shrinkwrap --runtime=null run rmm-tftf.yaml

To test |RMM| Live Firmware Activation (LFA) support, you can use the
``lfa-support.yaml`` overlay along with other overlays as needed:

    .. code-block:: shell

       shrinkwrap build --btvar=RMM_SRC=${PWD} --overlay=rmm-debug.yaml --overlay rmm-v1_1.yaml --overlay=lfa-support.yaml rmm-tftf.yaml --no-sync-all

To run the tests with MEC enabled :

    .. code-block:: shell

       shrinkwrap run --overlay model-enable-mec.yaml --overlay=lfa-support.yaml rmm-tftf.yaml

.. note::

      Note that ``runtime=null`` is specified for the run, as it must match
      the same setting as used on the build stage. Also, with this setting,
      the appropriate FVP (FVP_Base_RevC-2xAEMvA) needs to be present in the
      system ${PATH}.

      FVP version must be >= ``11.29.27`` when rmm-v1_1.yaml overlay is used.

-----

.. _Shrinkwrap: https://shrinkwrap.docs.arm.com
.. _Quick Start Guide: https://shrinkwrap.docs.arm.com/en/latest/userguide/quickstart.html#quick-start-guide
.. _3 world configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-3world.html
.. _4 world configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-4world.html
.. _TF-A-Tests: https://trustedfirmware-a-tests.readthedocs.io/en/latest/index.html
.. _btvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
.. _rtvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
.. _DA workflow: https://gitlab.geo.arm.com/software/linux-arm/linux-kernel-aneesh/-/commit/10cee3cb39ee53738fbb722181c9cd2b5f42189d
