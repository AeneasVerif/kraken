module

public import Lean.Widget.UserWidget
public import Kraken.ShowProgram
public meta import Lean.Widget.UserWidget
public meta import Kraken.ShowProgram

/-!
Infoview panel widget for rendering the current assembly program with directive cursors
(`●` for current, `○` for previous) separately from the local context and goal.
-/

namespace Kraken

open Lean Meta

public meta section

/-- Infoview panel widget displaying a Kraken assembly program with `●`/`○` cursors
    and an interactive window / full-program toggle. -/
@[widget_module]
def krakenProgramWidget : Lean.Widget.Module where
  javascript := "
import * as React from 'react';
const e = React.createElement;

function computeRows(directives, curr, prev, before, after, showAll) {
  const numDirs = directives.length;
  const clampedCurr = Math.min(curr, numDirs);
  const validPrev = (typeof prev === 'number' && prev !== clampedCurr && prev <= numDirs) ? prev : null;

  if (numDirs === 0) {
    return { rows: [{ kind: 'end', idx: 0, isCurr: true }], hiddenCount: 0, clampedCurr };
  }

  const mkRow = (i) => {
    if (i === numDirs) {
      return { kind: 'end', idx: i, isCurr: i === clampedCurr };
    }
    const marker = i === clampedCurr ? 'curr' : (validPrev === i ? 'prev' : null);
    return { kind: 'dir', idx: i, text: directives[i], marker };
  };

  if (showAll) {
    const rows = [];
    for (let i = 0; i < numDirs; i++) rows.push(mkRow(i));
    if (clampedCurr === numDirs || validPrev === numDirs) rows.push(mkRow(numDirs));
    return { rows, hiddenCount: 0, clampedCurr };
  }

  const maxIdx = clampedCurr === numDirs ? numDirs : numDirs - 1;
  let lo = Math.max(0, clampedCurr - before);
  let hi = Math.min(maxIdx, clampedCurr + after);
  let pre = null;
  let post = null;

  if (validPrev !== null) {
    if (validPrev < lo) {
      if (validPrev + 1 === lo) lo = validPrev;
      else pre = validPrev;
    } else if (validPrev > hi) {
      if (validPrev === hi + 1) hi = validPrev;
      else post = validPrev;
    }
  }

  const rows = [];
  let shownDirs = 0;
  if (pre !== null) {
    if (pre > 0) rows.push({ kind: 'ellipsis', key: 'e-pre-0' });
    rows.push(mkRow(pre));
    if (pre < numDirs) shownDirs++;
    rows.push({ kind: 'ellipsis', key: 'e-pre-1' });
  } else if (lo > 0) {
    rows.push({ kind: 'ellipsis', key: 'e-lo' });
  }

  for (let i = lo; i <= hi; i++) {
    rows.push(mkRow(i));
    if (i < numDirs) shownDirs++;
  }

  if (post !== null) {
    rows.push({ kind: 'ellipsis', key: 'e-post-0' });
    rows.push(mkRow(post));
    if (post < numDirs) shownDirs++;
    if (post + 1 < numDirs) rows.push({ kind: 'ellipsis', key: 'e-post-1' });
  } else if (hi + 1 < numDirs) {
    rows.push({ kind: 'ellipsis', key: 'e-hi' });
  }

  return { rows, hiddenCount: Math.max(0, numDirs - shownDirs), clampedCurr };
}

export default function KrakenProgramWidget(props) {
  const { name = '<program>', directives = [], curr = 0, prev = null, before = 2, after = 5 } = props || {};
  const [showAll, setShowAll] = React.useState(false);
  const rootRef = React.useRef(null);

  // Move the enclosing widget section above 'Tactic state' via CSS flex order
  // (no DOM reparenting, so React reconciliation stays intact; safely no-ops if layout differs).
  React.useLayoutEffect(() => {
    const root = rootRef.current;
    if (!root) return;

    let sectionEl = root;
    let container = null;
    while (sectionEl && sectionEl.parentElement) {
      const parent = sectionEl.parentElement;
      const hasTacticStateSibling = Array.from(parent.children).some((child) => {
        if (child === sectionEl) return false;
        const summary = child.matches('summary') ? child : child.querySelector('summary');
        const text = summary ? (summary.textContent || '') : '';
        return text.includes('Tactic state');
      });
      if (hasTacticStateSibling) {
        container = parent;
        break;
      }
      sectionEl = parent;
    }

    if (!container) return;

    const prevDisplay = container.style.display;
    const prevFlexDir = container.style.flexDirection;
    const prevOrder = sectionEl.style.order;

    container.style.display = 'flex';
    container.style.flexDirection = 'column';
    sectionEl.style.order = '-1';

    return () => {
      container.style.display = prevDisplay;
      container.style.flexDirection = prevFlexDir;
      sectionEl.style.order = prevOrder;
    };
  }, [name, curr, prev]);

  const numDirs = directives.length;
  const { rows, hiddenCount, clampedCurr } = computeRows(directives, curr, prev, before, after, showAll);
  const idxWidth = `${Math.max(1, String(numDirs).length)}ch`;
  const canToggle = showAll || hiddenCount > 0;

  const containerStyle = {
    border: '1px solid var(--vscode-panel-border, rgba(128,128,128,0.35))',
    borderRadius: '4px',
    backgroundColor: 'var(--vscode-editor-background, transparent)',
    margin: '4px 0',
    overflow: 'hidden',
  };

  const headerStyle = {
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'space-between',
    gap: '8px',
    padding: '4px 8px',
    backgroundColor: 'var(--vscode-editorWidget-background, rgba(128,128,128,0.08))',
    borderBottom: '1px solid var(--vscode-panel-border, rgba(128,128,128,0.25))',
    fontSize: '0.9em',
  };

  const buttonStyle = {
    background: 'var(--vscode-button-secondaryBackground, rgba(128,128,128,0.2))',
    color: 'var(--vscode-button-secondaryForeground, inherit)',
    border: '1px solid var(--vscode-panel-border, rgba(128,128,128,0.35))',
    borderRadius: '3px',
    padding: '1px 6px',
    fontSize: '0.85em',
    cursor: 'pointer',
  };

  const bodyStyle = {
    fontFamily: 'var(--vscode-editor-font-family, monospace)',
    fontSize: 'var(--vscode-editor-font-size, 12px)',
    lineHeight: '1.45',
    padding: '4px 0',
    overflowX: 'auto',
  };

  const renderRow = (row) => {
    if (row.kind === 'ellipsis') {
      return e('div', {
        key: row.key,
        style: {
          display: 'flex',
          padding: '0 8px 0 6px',
          borderLeft: '2px solid transparent',
          color: 'var(--vscode-descriptionForeground, #888)',
          userSelect: 'none',
        },
      },
        e('span', { style: { display: 'inline-block', width: idxWidth, marginRight: '8px' } }, ''),
        e('span', { style: { display: 'inline-block', width: '1.2em', marginRight: '6px' } }, ''),
        e('span', null, '···')
      );
    }

    const isCurr = row.kind === 'dir' ? row.marker === 'curr' : row.isCurr;
    const isPrev = row.kind === 'dir' ? row.marker === 'prev' : !row.isCurr;

    const rowStyle = {
      display: 'flex',
      alignItems: 'baseline',
      padding: '1px 8px 1px 6px',
      whiteSpace: 'pre',
      borderLeft: isCurr
        ? '2px solid var(--vscode-editorInfo-foreground, #3794ff)'
        : isPrev
          ? '2px solid var(--vscode-descriptionForeground, #888)'
          : '2px solid transparent',
      backgroundColor: isCurr
        ? 'var(--vscode-editor-lineHighlightBackground, rgba(55, 148, 255, 0.14))'
        : isPrev
          ? 'rgba(128, 128, 128, 0.08)'
          : 'transparent',
      fontWeight: isCurr ? 600 : 400,
    };

    const markerChar = isCurr ? '●' : (isPrev ? '○' : ' ');
    const markerColor = isCurr
      ? 'var(--vscode-editorInfo-foreground, #3794ff)'
      : 'var(--vscode-descriptionForeground, #888)';

    const isLabel = row.kind === 'dir' && row.text.trimEnd().endsWith(':');
    const textStyle = row.kind === 'end'
      ? { color: 'var(--vscode-descriptionForeground, #888)', fontStyle: 'italic' }
      : isLabel
        ? { color: 'var(--vscode-symbolIcon-functionForeground, var(--vscode-textLink-foreground, #4ec9b0))', fontWeight: 600 }
        : { color: 'var(--vscode-editor-foreground, inherit)' };

    return e('div', { key: `row-${row.kind}-${row.idx}`, style: rowStyle },
      e('span', {
        style: {
          display: 'inline-block',
          width: idxWidth,
          textAlign: 'right',
          marginRight: '8px',
          color: 'var(--vscode-editorLineNumber-foreground, #858585)',
          userSelect: 'none',
        },
      }, String(row.idx)),
      e('span', {
        style: {
          display: 'inline-block',
          width: '1.2em',
          textAlign: 'center',
          marginRight: '6px',
          color: markerColor,
          userSelect: 'none',
        },
      }, markerChar),
      e('span', { style: textStyle }, row.kind === 'end' ? '<end>' : row.text)
    );
  };

  return e('div', { ref: rootRef, style: containerStyle },
    e('div', { style: headerStyle },
      e('div', { style: { display: 'flex', alignItems: 'center', gap: '8px' } },
        e('span', { style: { fontFamily: 'var(--vscode-editor-font-family, monospace)', fontWeight: 600 } }, name),
        e('span', { style: { color: 'var(--vscode-descriptionForeground, #888)', fontFamily: 'var(--vscode-editor-font-family, monospace)' } }, `pc: ${clampedCurr}/${numDirs}`)
      ),
      canToggle
        ? e('button', { type: 'button', style: buttonStyle, onClick: () => setShowAll(!showAll) },
            showAll ? `Window (-${before}, +${after})` : `Show all (${numDirs})`)
        : null
    ),
    e('div', { style: bodyStyle }, rows.map(renderRow))
  );
}
"

/-- Validate `pp.kraken.program` and, when set to `"widget"`, save the Infoview panel widget
    onto `stx` for the given `goal` and `ShowProgramMeta`. -/
def saveProgramWidgetIfEnabled (goal : MVarId) (m : ShowProgramMeta) (stx : Syntax) : MetaM Unit := do
  let mode ← getShowProgramModeM
  if mode != .widget then
    return
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let (_, inner) := stripShowProgramMData target
    let some (_, progExpr, pcIdx?) := extractEventuallyProgramAndPc? inner | return
    let curr := pcIdx?.getD m.idx
    let some json ← buildProgramWidgetJson progExpr { m with idx := curr } | return
    Lean.Widget.savePanelWidgetInfo krakenProgramWidget.javascriptHash (pure json) stx

end

end Kraken
