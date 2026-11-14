// The custom `wiz/*` requests of the infoview protocol
// (wiz-notes/infoview-protocol.md), as TypeScript types.
export interface Position {
  line: number;
  character: number;
}

export interface Range {
  start: Position;
  end: Position;
}

export interface Location {
  uri: string;
  range: Range;
}

export interface SubtermTag {
  ref: number;
  kind: string;
  name?: string | null;
}

export type TaggedText =
  | { text: string }
  | { append: TaggedText[] }
  | { tag: [SubtermTag, TaggedText] };

export interface Hyp {
  names: string[];
  type: TaggedText;
  val?: TaggedText | null;
}

export interface InteractiveGoal {
  hyps?: Hyp[];
  type: TaggedText;
  goalPrefix?: string | null;
  userName?: string | null;
}

export interface Widget {
  title: string;
  html: string;
  range: Range;
  goals: string[];
}

export interface GoalsResult {
  goals: InteractiveGoal[];
  range: Range;
  session: number;
  messages?: string[];
  widgets?: Widget[];
}

export interface TermGoalResult {
  goal: InteractiveGoal;
  range: Range;
  session: number;
}

export type InfoKind =
  | 'syntax'
  | 'expansion'
  | 'import'
  | 'instance'
  | 'declaration'
  | 'message';

export interface InfoItem {
  kind: InfoKind;
  range: Range;
  title: string;
  text?: string | null;
  type?: TaggedText | null;
  location?: Location | null;
}

export interface InfoResult {
  items: InfoItem[];
  session: number;
}

export interface SubtermInfo {
  text: string;
  kind: string;
  name?: string | null;
  type?: TaggedText | null;
  definition?: Location | null;
  session: number;
}

export interface ElaboratedParams {
  uri: string;
  version?: number | null;
  session: number;
}
