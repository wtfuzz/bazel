// Copyright 2016 The Bazel Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package com.google.devtools.build.lib.rules;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.devtools.build.lib.actions.Artifact;
import com.google.devtools.build.lib.analysis.ConfiguredTarget;
import com.google.devtools.build.lib.analysis.FileProvider;
import com.google.devtools.build.lib.analysis.SkylarkProviders;
import com.google.devtools.build.lib.analysis.TransitiveInfoProvider;
import com.google.devtools.build.lib.analysis.config.BuildConfiguration;
import com.google.devtools.build.lib.cmdline.Label;
import com.google.devtools.build.lib.collect.nestedset.NestedSetBuilder;
import com.google.devtools.build.lib.collect.nestedset.Order;
import com.google.devtools.build.lib.concurrent.ThreadSafety.Immutable;
import com.google.devtools.build.lib.packages.Target;
import com.google.devtools.build.lib.syntax.ClassObject;
import com.google.devtools.build.lib.syntax.SkylarkNestedSet;

/**
 * This configured target pretends to be whatever type of target "actual" is, returning its
 * transitive info providers and target, but returning its own label.
 *
 * <p>Transitive info providers can also be overridden.
 */
@Immutable
public final class AliasConfiguredTarget implements ConfiguredTarget, ClassObject {
  private final ConfiguredTarget configuredTarget;
  private final ImmutableMap<Class<? extends TransitiveInfoProvider>, TransitiveInfoProvider>
      overrides;

  public AliasConfiguredTarget(ConfiguredTarget actual,
      ImmutableMap<Class<? extends TransitiveInfoProvider>, TransitiveInfoProvider> overrides) {
    configuredTarget = actual;
    this.overrides = overrides;
  }

  @Override
  public <P extends TransitiveInfoProvider> P getProvider(Class<P> provider) {
    if (overrides.containsKey(provider)) {
      return provider.cast(overrides.get(provider));
    }

    return configuredTarget == null ? null : configuredTarget.getProvider(provider);
  }

  @Override
  public Label getLabel() {
    return configuredTarget.getLabel();
  }

  @Override
  public Object get(String providerKey) {
    return configuredTarget == null ? null : configuredTarget.get(providerKey);
  }

  @Override
  public Target getTarget() {
    return configuredTarget == null ? null : configuredTarget.getTarget();
  }

  @Override
  public BuildConfiguration getConfiguration() {
    return configuredTarget.getConfiguration();
  }

  /* ClassObject methods */

  @Override
  public Object getValue(String name) {
    if (name.equals("label")) {
      return getLabel();
    } else if (name.equals("files")) {
      // A shortcut for files to build in Skylark. FileConfiguredTarget and RunleConfiguredTarget
      // always has FileProvider and Error- and PackageGroupConfiguredTarget-s shouldn't be
      // accessible in Skylark.
      return SkylarkNestedSet.of(Artifact.class, configuredTarget == null
          ? NestedSetBuilder.<Artifact>emptySet(Order.STABLE_ORDER)
          : getProvider(FileProvider.class).getFilesToBuild());
    }
    return configuredTarget == null ? null : configuredTarget.get(name);
  }

  @Override
  public ImmutableCollection<String> getKeys() {
    ImmutableList.Builder<String> result = ImmutableList.<String>builder().add("label", "files");
    if (configuredTarget != null) {
        result.addAll(configuredTarget.getProvider(SkylarkProviders.class).getKeys());
    }
    return result.build();
  }

  @Override
  public String errorMessage(String name) {
    // Use the default error message.
    return null;
  }
}
