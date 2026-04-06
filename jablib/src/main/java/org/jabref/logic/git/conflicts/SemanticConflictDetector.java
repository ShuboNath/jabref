package org.jabref.logic.git.conflicts;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.jabref.logic.bibtex.comparator.BibDatabaseDiff;
import org.jabref.logic.bibtex.comparator.BibEntryDiff;
import org.jabref.logic.git.merge.planning.util.ConflictRules;
import org.jabref.logic.git.model.MergePlan;
import org.jabref.model.database.BibDatabaseContext;
import org.jabref.model.entry.BibEntry;
import org.jabref.model.entry.field.Field;

import static com.google.common.collect.Sets.union;

/// Detects semantic merge conflicts between base, local, and remote.
///
/// Strategy:
/// Instead of computing full diffs from base to local/remote, we simulate a Git-style merge
/// by applying the diff between base and remote onto local (`result := local + remoteDiff`).
///
/// Caveats:
/// - Only entries with the same citation key are considered matching.
/// - Entries without citation keys are currently ignored.
/// - Changing a citation key is not supported and is treated as deletion + addition.
@Deprecated
public class SemanticConflictDetector {
    public static List<ThreeWayEntryConflict> detectConflicts(BibDatabaseContext base, BibDatabaseContext local, BibDatabaseContext remote) {
        // 1. get diffs between base, local and remote
        BibDatabaseDiff localDiff = BibDatabaseDiff.compare(base, local);
        BibDatabaseDiff remoteDiff = BibDatabaseDiff.compare(base, remote);

        // 2. Union of all citationKeys that were changed (on either side)
        EntryTriples triples = EntryTriples.from(base, local, remote);

        // 3. Build a map from citationKey -> BibEntryDiff for both local and remote diffs
        Map<String, BibEntryDiff> localDiffMap = indexByCitationKey(localDiff.getEntryDifferences());
        Map<String, BibEntryDiff> remoteDiffMap = indexByCitationKey(remoteDiff.getEntryDifferences());
        Set<String> allKeys = union(localDiffMap.keySet(), remoteDiffMap.keySet());

        List<ThreeWayEntryConflict> conflicts = new ArrayList<>();

        // 4. Build full 3-way entry maps (key -> entry) from each database
        for (String key : allKeys) {
            BibEntry baseEntry = triples.baseMap.get(key);
            BibEntry localEntry = resolveEntry(key, localDiffMap.get(key), triples.localMap);
            BibEntry remoteEntry = resolveEntry(key, remoteDiffMap.get(key), triples.remoteMap);

            // 5. If this triplet results in a conflict, collect it
            detectEntryConflict(baseEntry, localEntry, remoteEntry).ifPresent(conflicts::add);
        }

        return conflicts;
    }

    /// Detect entry-level conflicts among base, local, and remote versions of an entry.
    ///
    /// @param base   the entry in the common ancestor
    /// @param local  the entry in the local version
    /// @param remote the entry in the remote version
    /// @return optional conflict (if detected)
    private static Optional<ThreeWayEntryConflict> detectEntryConflict(BibEntry base,
                                                                       BibEntry local,
                                                                       BibEntry remote) {
        return ConflictRules.detectEntryConflict(base, local, remote);
    }

    /// Compares base and remote, finds all semantic-level changes (new entries, updated fields), and builds a patch plan.
    /// This plan is meant to be applied to local during merge:
    /// result = local + (remote − base)
    ///
    /// @param base   The base version of the database.
    /// @param remote The remote version to be merged.
    /// @return A {@link MergePlan} describing how to update the local copy with remote changes.
    public static MergePlan extractMergePlan(BibDatabaseContext base, BibDatabaseContext local, BibDatabaseContext remote) {
        EntryTriples triples = EntryTriples.from(base, local, remote);

        Map<String, Map<Field, String>> fieldPatches = new LinkedHashMap<>();
        List<BibEntry> newEntries = new ArrayList<>();
        List<String> deletedEntryKeys = new ArrayList<>();

        for (Map.Entry<String, BibEntry> remoteEntryPair : triples.remoteMap.entrySet()) {
            String key = remoteEntryPair.getKey();
            BibEntry remoteEntry = remoteEntryPair.getValue();
            BibEntry baseEntry = triples.baseMap.get(key);
            BibEntry localEntry = triples.localMap.get(key);

            // Case 1: Both sides added the same key, if there is no disagreement on overlapping fields -> add as a union
            if (baseEntry == null && localEntry != null) {
                if (!hasOverlappingFieldDisagreement(localEntry, remoteEntry)) {
                    newEntries.add(unionEntry(localEntry, remoteEntry));
                }
                continue;
            }

            // Case 2: Added only on the remote side
            if (baseEntry == null && localEntry == null) {
                newEntries.add(remoteEntry);
                continue;
            }

            // Case 3: Base exists — generate patches that apply only where local kept the base value
            if (baseEntry != null) {
                Map<Field, String> patch = computeFieldPatch(baseEntry, localEntry, remoteEntry);
                if (!patch.isEmpty()) {
                    fieldPatches.put(key, patch);
                }
            }
        }

        return new MergePlan(fieldPatches, newEntries, deletedEntryKeys);
    }

    /// Compares base and remote and constructs a patch at the field level. null == the field is deleted.
    ///
    /// - Apply remote change when local kept base value (including deletions: null);
    /// - If both sides changed to the same value, no patch needed;
    /// - Fallback: if a divergence is still observed, do not override local; skip this field,
    ///
    /// @param base   base version
    /// @param local  local version
    /// @param remote remote version
    /// @return A map from field to new value
    private static Map<Field, String> computeFieldPatch(BibEntry base, BibEntry local, BibEntry remote) {
        Map<Field, String> patch = new LinkedHashMap<>();

        if (remote == null) {
            return patch;
        }

        Stream.concat(base.getFields().stream(), remote.getFields().stream())
              .distinct()
              .filter(field -> !isMetaField(field))
              .forEach(field -> {
                  String baseValue = base.getField(field).orElse(null);
                  String remoteValue = remote.getField(field).orElse(null);
                  String localValue = local == null ? null : local.getField(field).orElse(null);

                  if (Objects.equals(baseValue, remoteValue)) {
                      return;
                  }
                  if (Objects.equals(localValue, baseValue)) {
                      patch.put(field, remoteValue);
                      return;
                  }
                  if (Objects.equals(localValue, remoteValue)) {
                      return;
                  }
              });
        return patch;
    }

    /// Converts a List of BibEntryDiff into a Map where the key is the citation key,
    /// and the value is the corresponding BibEntryDiff.
    ///
    /// Notes:
    /// - Only entries with a citation key are included (entries without a key cannot be uniquely identified during merge).
    /// - Entries that represent additions (base == null) or deletions (new == null) are also included.
    /// - If multiple BibEntryDiffs share the same citation key (rare), the latter one will overwrite the former.
    ///
    /// @param entryDiffs A list of entry diffs produced by BibDatabaseDiff
    /// @return A map from citation key to corresponding BibEntryDiff
    private static Map<String, BibEntryDiff> indexByCitationKey(List<BibEntryDiff> entryDiffs) {
        Map<String, BibEntryDiff> result = new LinkedHashMap<>();

        for (BibEntryDiff diff : entryDiffs) {
            Optional<String> citationKey = Optional.ofNullable(diff.newEntry())
                                                   .flatMap(BibEntry::getCitationKey)
                                                   .or(() -> Optional.ofNullable(diff.originalEntry())
                                                                     .flatMap(BibEntry::getCitationKey));
            citationKey.ifPresent(key -> result.put(key, diff));
        }

        return result;
    }

    private static Map<String, BibEntry> getCitationKeyToEntryMap(BibDatabaseContext context) {
        return context.getDatabase().getEntries().stream()
                      .filter(entry -> entry.getCitationKey().isPresent())
                      .collect(Collectors.toMap(
                              entry -> entry.getCitationKey().get(),
                              Function.identity(),
                              (existing, replacement) -> replacement,
                              LinkedHashMap::new
                      ));
    }

    private static BibEntry resolveEntry(String key, BibEntryDiff diff, Map<String, BibEntry> fullMap) {
        if (diff == null) {
            return fullMap.get(key);
        }
        return diff.newEntry();
    }

    private static boolean hasOverlappingFieldDisagreement(BibEntry left, BibEntry right) {
        Set<Field> overlap = new LinkedHashSet<>(left.getFields());
        overlap.retainAll(right.getFields());
        overlap.removeIf(SemanticConflictDetector::isMetaField);
        for (Field overlappingField : overlap) {
            String leftFieldValue = left.getField(overlappingField).orElse(null);
            String rightFieldValue = right.getField(overlappingField).orElse(null);
            if (!leftFieldValue.equals(rightFieldValue)) {
                return true;
            }
        }
        return false;
    }

    private static BibEntry unionEntry(BibEntry localAdded, BibEntry remoteAdded) {
        BibEntry merged = new BibEntry(localAdded);
        for (Field field : remoteAdded.getFields()) {
            if (isMetaField(field)) {
                continue;
            }
            if (merged.getField(field).isEmpty()) {
                merged.setField(field, remoteAdded.getField(field).get());
            }
        }
        return merged;
    }

    private static boolean isMetaField(Field f) {
        String name = f.getName();
        return name.startsWith("_") || "_jabref_shared".equalsIgnoreCase(name);
    }

    static final class EntryTriples {
        final Map<String, BibEntry> baseMap;
        final Map<String, BibEntry> localMap;
        final Map<String, BibEntry> remoteMap;

        private EntryTriples(Map<String, BibEntry> baseMap,
                             Map<String, BibEntry> localMap,
                             Map<String, BibEntry> remoteMap) {
            this.baseMap = baseMap;
            this.localMap = localMap;
            this.remoteMap = remoteMap;
        }

        static EntryTriples from(BibDatabaseContext base,
                                 BibDatabaseContext local,
                                 BibDatabaseContext remote) {
            return new EntryTriples(
                    getCitationKeyToEntryMap(base),
                    getCitationKeyToEntryMap(local),
                    getCitationKeyToEntryMap(remote)
            );
        }
    }
}
