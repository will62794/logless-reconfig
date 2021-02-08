# Overview

This directory contains several specifications that are needed to define and verify various aspects of MongoDB's logless reconfiguration protocol, *MongoRaftReconfig*. Below is an overview of the specifications included in this directory and what they are used for.

- [MongoRaftReconfig.tla](MongoRaftReconfig.tla): The logless dynamic reconfiguration protocol for the MongoDB replication system. It is specified as a composition of two subprotocols, MongoStaticRaft and MongoLoglessDynamicRaft.
- [MongoStaticRaft.tla](MongoStaticRaft.tla): The static MongoDB replication protocol, without dynamic reconfiguration.
- [MongoLoglessDynamicRaft.tla](MongoLoglessDynamicRaft.tla): A logless variant of MongoDB's replication protocol that allows for dynamic reconfiguration.
- [MongoSafeWeakRaft.tla](MongoSafeWeakRaft.tla): An abstract, safe version of the MongoDB replication protocol that does not depend on strict quorum overlap.
- [MongoLoglessDynamicRaftRefinement](MongoLoglessDynamicRaftRefinement.tla): Used for defining a refinement mapping from MongoLoglessDynamicRaft to MongoSafeWeakRaft It extends MongoLoglessDynamicRaft with auxiliary variables that are necessary to define this mapping.
