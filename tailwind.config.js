/** Tailwind settings for ParlTrack Canada. Colours come from CSS variables (see input.css) so dark mode can swap them. */
const v = (n) => `rgb(var(--${n}) / <alpha-value>)`;

module.exports = {
  darkMode: 'class',
  content: ['./templates/**/*.html'],
  safelist: ['hidden', 'inline-flex', 'opacity-40'],
  theme: {
    extend: {
      fontFamily: {
        sans: ['Inter', 'ui-sans-serif', 'system-ui', '-apple-system', 'Segoe UI', 'Roboto', 'sans-serif'],
        serif: ['"Source Serif 4"', 'Georgia', 'Cambria', 'serif'],
      },
      colors: {
        canvas: v('canvas'), paper: v('paper'), night: v('night'),
        maple: { 50: v('maple-50'), 100: v('maple-100'), 600: v('maple-600'), 700: v('maple-700') },
        ink: {
          50: v('ink-50'), 100: v('ink-100'), 200: v('ink-200'), 400: v('ink-400'), 500: v('ink-500'),
          600: v('ink-600'), 700: v('ink-700'), 800: v('ink-800'), 900: v('ink-900'),
        },
      },
    },
  },
};
